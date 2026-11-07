import LSys
open LSys
def main : IO Unit := do
  let mut bad := 0; let mut cnt := 0
  let mut seed : Nat := 777
  let next (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
  for _ in [0:150] do
    seed := next seed; let n := seed % 4
    seed := next seed; let ma := seed % 2 + 1
    seed := next seed; let mr := seed % 3
    seed := next seed; let ae : Bool := decide (seed % 5 < 2)
    seed := next seed; let sigma := if seed % 3 == 0 then [0,1] else if seed % 3 == 1 then [1] else [0,2]
    seed := next seed; let len := seed % 6
    let mut w : List Nat := []
    for _ in [0:len] do
      seed := next seed; w := (seed % 3) :: w
    cnt := cnt + 1
    if !(check sigma ⟨ma, mr, ae⟩ w n) then
      bad := bad + 1; IO.println s!"MISMATCH w={w} n={n} B=({ma},{mr},{ae}) sigma={sigma}"
  IO.println s!"cases {cnt} mismatches {bad}"
