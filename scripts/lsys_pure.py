"""
Pure (mutation-free) inverse D0L search. Same algorithm as lsys_infer.infer,
written as total recursive functions over immutable state so it can be
transcribed to Lean.

State:
  rules : dict  sym -> (body: tuple, closed: bool)   (immutable: we copy on write)
  stack : tuple of (sym, depth, child_index)
  pos   : int   number of target characters matched so far
Leaves live at depth n+1; the pseudo-symbol START at depth 0 holds the axiom.
"""
from lsys_infer import LSystem, START


def minexp(rules, allow_empty, n, sym, d):
    if d == n + 1:
        return 1
    r = rules.get(sym)
    if r is None or (len(r[0]) == 0 and not r[1]):
        return 0 if allow_empty else 1
    return sum(minexp(rules, allow_empty, n, c, d + 1) for c in r[0])


def need(rules, allow_empty, n, stack):
    tot = 0
    for sym, d, i in stack:
        body, closed = rules.get(sym, ((), False))
        if i == 0 and len(body) == 0 and not closed and not allow_empty:
            tot += 1
        tot += sum(minexp(rules, allow_empty, n, c, d + 1) for c in body[i:])
    return tot


def to_key(rules, sigma, max_rule):
    """Canonical hashable form: (axiom, a rule for every symbol of sigma)."""
    def body(a):
        b, c = rules.get(a, ((), False))
        return "".join(b) if c else ("" if max_rule == 0 else a)
    return ("".join(rules[START][0]), tuple(sorted((a, body(a)) for a in sigma)))


def search(w, n, sigma, maxlen, allow_empty, rules, stack, pos):
    """Return the set of all completions of this state."""
    if not stack:
        return {to_key(rules, sigma, maxlen("x"))} if pos == len(w) else set()
    if pos + need(rules, allow_empty, n, stack) > len(w):
        return set()

    sym, d, i = stack[-1]
    body, closed = rules.get(sym, ((), False))
    rules = {**rules, sym: (body, closed)}
    rest = stack[:-1]

    if i < len(body):                         # expand child i
        child = body[i]
        nxt = rest + ((sym, d, i + 1),)
        if d + 1 == n + 1:
            if pos < len(w) and w[pos] == child:
                return search(w, n, sigma, maxlen, allow_empty, rules, nxt, pos + 1)
            return set()
        return search(w, n, sigma, maxlen, allow_empty, rules,
                      nxt + ((child, d + 1, 0),), pos)

    if closed:                                # node finished
        return search(w, n, sigma, maxlen, allow_empty, rules, rest, pos)

    out = set()
    if len(body) >= 1 or (allow_empty and sym != START):   # option A: close (never an empty axiom)
        out |= search(w, n, sigma, maxlen, allow_empty,
                      {**rules, sym: (body, True)}, rest, pos)
    if len(body) < maxlen(sym):               # option B: append one more symbol
        cands = ([w[pos]] if pos < len(w) and w[pos] in sigma else []) if d + 1 == n + 1 else sigma
        for c in cands:
            out |= search(w, n, sigma, maxlen, allow_empty,
                          {**rules, sym: (body + (c,), False)}, stack, pos)
    return out


def infer_pure(w, n, max_axiom=3, max_rule=4, allow_empty=False, hidden=0, sigma=None):
    if sigma is None:
        base = sorted(set(w))
        sigma = tuple(base + [c for c in "XYZUVW" if c not in w][:hidden])
    sigma = tuple(sigma)
    if (0 if allow_empty else 1) > max_rule:
        return []
    maxlen = lambda s: max_axiom if s == START else max_rule
    keys = search(w, n, sigma, maxlen, allow_empty, {}, ((START, 0, 0),), 0)
    sols = [LSystem(a, dict(r)) for a, r in keys]
    for s in sols:
        assert s.derive(n) == w
    return sorted(sols, key=lambda s: (s.size(), len(s.rules), s.axiom))


if __name__ == "__main__":
    import sys
    sys.setrecursionlimit(10000)
    for s in infer_pure("abaababaabaab", 5)[:3]:
        print(s)
