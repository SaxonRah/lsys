import sys, itertools, time, json
sys.setrecursionlimit(10000)
from lsys_infer import infer
def solve(w,n,k=50):
    L=len(w)
    return infer(w,n,max_axiom=L-1,max_rule=L,allow_empty=False,hidden=0,max_solutions=k)
def canon_word(w):  # symmetry: a/b swap, reversal
    sw=w.translate(str.maketrans('ab','ba'))
    return min(w, sw, w[::-1], sw[::-1])
data={}
for n in (3,4,5,6):
    t=time.time()
    data[n]={}
    for L in range(2,13):
        seen=set(); solv=[]
        for bits in itertools.product('ab',repeat=L):
            w=''.join(bits)
            if 'a' not in w or 'b' not in w: continue
            c=canon_word(w)
            if c in seen: continue
            seen.add(c)
            s=solve(w,n)
            if s: solv.append((w,s))
        data[n][L]=solv
        print(f"n={n} L={L}: {len(solv)}/{len(seen)} classes solvable  minax={min((len(x[1][0].axiom) for x in solv),default=None)}", flush=True)
    print("time",round(time.time()-t,1))
json.dump({n:{L:[(w,[(s.axiom,s.rules) for s in ss]) for w,ss in v.items()] if False else [(w,[(s.axiom,s.rules) for s in ss]) for w,ss in v] for L,v in d.items()} for n,d in data.items()}, open('/home/claude/explore.json','w'))
