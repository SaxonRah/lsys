import sys, itertools, time, re
sys.setrecursionlimit(10000)
from lsys_infer import infer
def solve(w,n):
    L=len(w); return infer(w,n,max_axiom=L-1,max_rule=L,allow_empty=False,hidden=0,max_solutions=1)
def F1(w,n):
    for x,y in (('a','b'),('b','a')):
        runs=w.split(y)                      # x-runs: leading, inner..., trailing
        if len(runs)<2: continue
        inner=runs[1:-1]
        if all(len(r)>=n for r in inner) and (len(runs[0])>=n or len(runs[-1])>=n):
            return True
    return False
MAXL=int(__import__("os").environ.get("MAXL","13"))
def canon(w):
    sw=w.translate(str.maketrans('ab','ba')); return min(w,sw,w[::-1],sw[::-1])
for n in [int(a) for a in sys.argv[1:]]:
    t=time.time(); bad=[]
    for L in range(2,MAXL+1):
        seen=set()
        for bits in itertools.product('ab',repeat=L):
            w=''.join(bits)
            if 'a' not in w or 'b' not in w: continue
            c=canon(w)
            if c in seen: continue
            seen.add(c)
            s=bool(solve(w,n)); f=F1(w,n)
            if s!=f: bad.append((L,w,'solvable-not-F1' if s else 'F1-not-solvable'))
    print(f"n={n}: threshold 2^(n//2)={2**(n//2)}; mismatches:", [(L,w,k) for L,w,k in bad][:12], f"... total {len(bad)}  ({time.time()-t:.0f}s)")
    print("   first non-F1 solvable length:", min((L for L,w,k in bad if k=='solvable-not-F1'),default=None),
          "  any F1-not-solvable:", any(k=='F1-not-solvable' for _,_,k in bad))
