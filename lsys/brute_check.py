"""Brute-force definition of Sol(w,n,B) and equality check against infer."""
import itertools, random
from lsys_infer import LSystem, infer

def used_symbols(S, n):
    """Symbols that actually get rewritten in derive 0..n-1."""
    used, s = set(), S.axiom
    for _ in range(n):
        used |= set(s); s = S.step(s)
    return used

def canon(S, n):
    u = used_symbols(S, n)
    return (S.axiom, tuple(sorted((k, v) for k, v in S.rules.items() if k in u)))

def brute(w, n, max_axiom, max_rule, allow_empty=False, hidden=0):
    base = sorted(set(w)); sigma = base + [c for c in "XYZUVW" if c not in w][:hidden]
    lo = 0 if allow_empty else 1
    def strings(lo_, hi): 
        for L in range(lo_, hi+1):
            for t in itertools.product(sigma, repeat=L): yield "".join(t)
    out = set()
    for ax in strings(1, max_axiom):
        for rs in itertools.product(list(strings(lo, max_rule)), repeat=len(sigma)):
            S = LSystem(ax, dict(zip(sigma, rs)))
            if S.derive(n) == w: out.add(canon(S, n))
    return out

random.seed(1)
bad = 0
for trial in range(300):
    n = random.randint(1, 3)
    B = dict(max_axiom=random.randint(1,2), max_rule=random.randint(1,2),
             allow_empty=random.random()<0.3, hidden=random.randint(0,1))
    # generate w by sampling a random system so Sol is often nonempty
    sigma = random.sample("ab", random.randint(1,2))
    lo = 0 if B['allow_empty'] else 1
    S0 = LSystem("".join(random.choices(sigma, k=random.randint(1,B['max_axiom']))),
                 {c: "".join(random.choices(sigma, k=random.randint(lo,B['max_rule']))) for c in sigma})
    w = S0.derive(n)
    if not (1 <= len(w) <= 12): continue
    got = {canon(S, n) for S in infer(w, n, max_solutions=10**9, **B)}
    exp = brute(w, n, **B)
    if got != exp:
        bad += 1; print("MISMATCH", repr(w), n, B); print(" infer-only:", got-exp); print(" brute-only:", exp-got)
print("mismatches:", bad)
