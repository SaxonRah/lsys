"""
Inverse L-system inference (D0L): given a target string w and a number of
derivation steps n, find axiom + rewrite rules such that applying the rules
n times to the axiom yields exactly w.

Method: lazy-expansion backtracking over a derivation tree of uniform depth.
Rules are built incrementally; a rule f(a) is shared across every occurrence
of `a` at every level, so a guess made anywhere constrains the whole tree.
Leaves are matched against w left to right and mismatches prune immediately.
"""
import sys
from dataclasses import dataclass

sys.setrecursionlimit(10000)

START = "^"  # pseudo-symbol whose "rule" is the axiom


@dataclass(frozen=True)
class LSystem:
    axiom: str
    rules: dict  # symbol -> successor string

    def step(self, s):
        return "".join(self.rules.get(c, c) for c in s)

    def derive(self, n):
        s = self.axiom
        for _ in range(n):
            s = self.step(s)
        return s

    def size(self):
        return len(self.axiom) + sum(len(v) for v in self.rules.values())

    def __str__(self):
        rs = ", ".join(f"{k}->{v or 'ε'}" for k, v in sorted(self.rules.items()))
        return f"axiom={self.axiom!r}  rules=[{rs}]  size={self.size()}"


def infer(w, n, max_axiom=3, max_rule=4, allow_empty=False,
          hidden=0, max_solutions=200, sigma=None):
    """Enumerate D0L systems S with S.derive(n) == w, within size bounds.
    sigma defaults to the symbols of w plus `hidden` extra symbols."""
    if sigma is None:
        base = sorted(set(w))
        hidden_syms = [c for c in "XYZUVW" if c not in w][:hidden]
        sigma = base + hidden_syms
    lo = 0 if allow_empty else 1
    if lo > max_rule:          # no legal rule body exists: the solution set is empty
        return []

    rules = {}
    closed = {}
    found = {}

    def maxlen(sym):
        return max_axiom if sym == START else max_rule

    def minexp(sym, d, memo):
        """Lower bound on leaves produced by sym at depth d (leaves at n+1)."""
        if d == n + 1:
            return 1
        key = (sym, d)
        if key in memo:
            return memo[key]
        r = rules.get(sym)
        if r is None or (len(r) == 0 and not closed.get(sym)):
            v = 0 if allow_empty else 1
        else:
            v = sum(minexp(c, d + 1, memo) for c in r)
        memo[key] = v
        return v

    def remaining_need(stack):
        memo = {}
        need = 0
        for sym, d, i in stack:
            r = rules.get(sym, [])
            if i == 0 and len(r) == 0 and not closed.get(sym) and not allow_empty:
                need += 1
            for c in r[i:]:
                need += minexp(c, d + 1, memo)
        return need

    def default_body(a):          # shortest legal body for a never-rewritten symbol
        return "" if max_rule == 0 else a

    def record():
        sysm = LSystem("".join(rules[START]),
                       {a: ("".join(rules[a]) if closed.get(a) else default_body(a))
                        for a in sigma})
        found.setdefault((sysm.axiom, tuple(sorted(sysm.rules.items()))), sysm)

    def rec(stack, pos):
        if len(found) >= max_solutions:
            return
        if not stack:
            if pos == len(w):
                record()
            return
        if pos + remaining_need(stack) > len(w):
            return

        sym, d, i = stack[-1]
        r = rules.setdefault(sym, [])
        closed.setdefault(sym, False)

        if i < len(r):  # expand next child
            child = r[i]
            stack[-1][2] += 1
            if d + 1 == n + 1:
                if pos < len(w) and w[pos] == child:
                    rec(stack, pos + 1)
            else:
                stack.append([child, d + 1, 0])
                rec(stack, pos)
                stack.pop()
            stack[-1][2] -= 1
            return

        if closed[sym]:  # finished this node
            fr = stack.pop()
            rec(stack, pos)
            stack.append(fr)
            return

        # rule still open: either close it here (never an empty axiom), or append a symbol
        if len(r) >= 1 or (allow_empty and sym != START):
            closed[sym] = True
            fr = stack.pop()
            rec(stack, pos)
            stack.append(fr)
            closed[sym] = False

        if len(r) < maxlen(sym):
            if d + 1 == n + 1:
                cands = [w[pos]] if pos < len(w) and w[pos] in sigma else []
            else:
                cands = sigma
            for c in cands:
                r.append(c)
                rec(stack, pos)
                r.pop()

    rec([[START, 0, 0]], 0)
    sols = sorted(found.values(), key=lambda s: (s.size(), len(s.rules), s.axiom))
    for s in sols:
        assert s.derive(n) == w, (s, s.derive(n))
    return sols


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("target")
    ap.add_argument("n", type=int)
    ap.add_argument("--max-axiom", type=int, default=3)
    ap.add_argument("--max-rule", type=int, default=4)
    ap.add_argument("--hidden", type=int, default=0)
    ap.add_argument("--empty", action="store_true")
    ap.add_argument("--top", type=int, default=10)
    a = ap.parse_args()
    sols = infer(a.target, a.n, a.max_axiom, a.max_rule, a.empty, a.hidden)
    print(f"{len(sols)} solutions; best {a.top}:")
    for s in sols[:a.top]:
        print(" ", s)
