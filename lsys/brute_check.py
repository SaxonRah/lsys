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

def brute(w, n, max_axiom, max_rule, allow_empty=False, hidden=0, sigma=None):
    if sigma is None:
        base = sorted(set(w)); sigma = base + [c for c in "XYZUVW" if c not in w][:hidden]
    sigma = list(sigma)
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

if __name__ == "__main__":
  random.seed(1)
  bad = 0; cnt = 0
  for trial in range(600):
    n = random.randint(0, 3)
    B = dict(max_axiom=random.randint(1,2), max_rule=random.randint(0,2),
             allow_empty=random.random()<0.4)
    # alphabet independent of w: covers w ⊄ sigma, w = [], maxRule = 0
    sig = random.sample("abc", random.randint(1,2))
    lo = 0 if B['allow_empty'] else 1
    if random.random() < 0.7 and lo <= B['max_rule']:
        S0 = LSystem("".join(random.choices(sig, k=random.randint(1,B['max_axiom']))),
                     {c: "".join(random.choices(sig, k=random.randint(lo,B['max_rule']))) for c in sig})
        w = S0.derive(n)
    else:
        w = "".join(random.choices("abc", k=random.randint(0,4)))
    if len(w) > 12: continue
    cnt += 1
    got = {canon(S, n) for S in infer(w, n, max_solutions=10**9, sigma=sig, **B)}
    exp = brute(w, n, sigma=sig, **B)
    if got != exp:
        bad += 1; print("MISMATCH", repr(w), n, B, sig); print(" infer-only:", got-exp); print(" brute-only:", exp-got)
  print("cases", cnt, "mismatches:", bad)
