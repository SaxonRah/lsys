"""Python-vs-Lean parity test: run `lsys_infer.infer` and the compiled Lean search
(`lake exe lsys --json`) on the same instances and compare canonical solution sets.

    python3 lsys/crosscheck.py [--gen N --seed S]   # default: use test/instances.json
Expects 0 mismatches. Requires `lake build` to have produced .lake/build/bin/lsys.
"""
import json, os, random, subprocess, sys
sys.path.insert(0, os.path.dirname(__file__))
from lsys_infer import LSystem, infer
from brute_check import canon

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "lsys")
INST = os.path.join(ROOT, "test", "instances.json")

def gen(k, seed):
    rng = random.Random(seed); out = []
    for _ in range(k):
        L = rng.randint(1, 10); n = rng.randint(1, 4)
        w = "".join(rng.choice("ab" if rng.random() < .8 else "abc") for _ in range(L))
        out.append({"w": w, "n": n, "max_axiom": rng.randint(1, 3),
                    "max_rule": rng.randint(1, 3), "allow_empty": rng.random() < .3,
                    "hidden": rng.choice([0, 0, 1])})
    return out

def lean_sols(i):
    args = [EXE, i["w"], str(i["n"]), "--max-axiom", str(i["max_axiom"]),
            "--max-rule", str(i["max_rule"]), "--hidden", str(i["hidden"]), "--json"]
    if i["allow_empty"]: args.append("--empty")
    out = subprocess.run(args, capture_output=True, text=True, check=True).stdout
    return {canon(LSystem(d["axiom"], d["rules"]), i["n"]) for d in map(json.loads, out.splitlines())}

def py_sols(i):
    return {canon(S, i["n"]) for S in infer(i["w"], i["n"], i["max_axiom"], i["max_rule"],
                                            i["allow_empty"], i["hidden"], max_solutions=10**9)}

if __name__ == "__main__":
    if "--gen" in sys.argv:
        k = int(sys.argv[sys.argv.index("--gen") + 1])
        seed = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 0
        json.dump(gen(k, seed), open(INST, "w"), indent=0)
    inst = json.load(open(INST)); bad = 0
    for i in inst:
        p, l = py_sols(i), lean_sols(i)
        if p != l:
            bad += 1; print("MISMATCH", i, "\n  python-only", p - l, "\n  lean-only", l - p)
    print(f"instances {len(inst)} mismatches {bad}")
    sys.exit(1 if bad else 0)
