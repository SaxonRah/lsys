"""Independent finite checks supporting bounds for SaxonRah/lsys.
Only uses Python's standard library. These checks are NOT Lean proofs.
"""
from itertools import product
from math import comb

def count_direct(s):
    return sum(comb(t+2,2) * (2**t) for t in range(s+1))

def direct_formula(s):
    return 2**s*(s*s+s+2)-1

def insertion_optimum(w,n,x):
    """Exact minimum axiom length and size among insertion systems fixing x.
    Returns None when no strict insertion with a shorter axiom exists.
    """
    y = 'b' if x == 'a' else 'a'
    if y not in w or n < 1:
        return None
    rs = [len(r) for r in w.split(y)]
    middle = min((r//n for r in rs[1:-1]),default=10**20)
    C = min(rs[0]//n + rs[-1]//n, middle)
    if not C:
        return None
    p = min(C,rs[0]//n); q = C-p
    u = [rs[0]-n*p] + [r-n*C for r in rs[1:-1]] + [rs[-1]-n*q]
    assert min(u)>=0
    axiom = ''.join((x*u[i]+y) for i in range(len(u)-1)) + x*u[-1]
    rules={x:x,y:x*p+y+x*q}
    z=axiom
    for _ in range(n):
        z=''.join(rules[c] for c in z)
    assert z==w
    return {'max_insertion_p_plus_q':C,'axiom':axiom,
            'axiom_length':len(axiom),'description_size':len(axiom)+C+2,
            'p':p,'q':q}

def brute_insertion_optimum(w,n,x):
    y='b' if x=='a' else 'a'
    if y not in w:return None
    rs=[len(r) for r in w.split(y)]
    best=None
    for p in range(len(w)+1):
      for q in range(len(w)+1):
        if not p+q:continue
        if rs[0]<n*p or rs[-1]<n*q or any(r<n*(p+q) for r in rs[1:-1]):continue
        size=len(w)+2-(n*w.count(y)-1)*(p+q)
        ax=len(w)-n*w.count(y)*(p+q)
        val=(ax,size)
        if best is None or val<best:best=val
    return best

def matmul(a,b):
    return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])

def matpow(m,n):
    result=(1,0,0,1)
    while n:
        if n&1:result=matmul(result,m)
        m=matmul(m,m);n//=2
    return result

def incidence_solutions(n,A,B,max_axiom):
    """Necessary Parikh-vector test, exact for all relevant non-erasing matrices.
    Entries at most output length suffice: used columns cannot be longer than the
    output under non-erasing rewrites; unused rules can be replaced by identities.
    """
    L=A+B;sol=[]; examined=0
    for aa in range(L+1):
      for ba in range(L+1-aa): # nonzero first column
        if aa+ba==0:continue
        for ab in range(L+1):
          for bb in range(L+1-ab):
            if ab+bb==0:continue
            m=(aa,ab,ba,bb)
            pm=matpow(m,n)
            if pm[0]>A and pm[1]>A:continue
            if pm[2]>B and pm[3]>B:continue
            examined+=1
            for u in range(max_axiom+1):
              for v in range(max_axiom-u+1):
                if not u+v:continue
                if pm[0]*u+pm[1]*v==A and pm[2]*u+pm[3]*v==B:
                    sol.append((m,(u,v)))
    return sol,examined

if __name__=='__main__':
    for s in range(0,40): assert count_direct(s)==direct_formula(s)
    print('PASS exact binary description count A(s), s=0..39')
    checked=0
    for L in range(2,11):
      for bits in product('ab',repeat=L):
        w=''.join(bits)
        for n in range(1,7):
          for x in 'ab':
            formula=insertion_optimum(w,n,x)
            brute=brute_insertion_optimum(w,n,x)
            if formula is None:assert brute is None
            else:assert (formula['axiom_length'],formula['description_size'])==brute
            checked+=1
    print('PASS exact insertion optimum vs brute p,q,',checked,'cases')
    for n,A,B,cap in [(3,3,8,3),(4,5,16,5),(4,5,16,6)]:
        ss,examined=incidence_solutions(n,A,B,cap)
        print(f'Parikh: n={n}, target=a^{A}b^{B}, axiom<={cap}: solutions={ss}, candidate matrices={examined}')
        if cap in [3,5]: assert not ss
        else: assert ((1,0,0,2),(5,1)) in ss
