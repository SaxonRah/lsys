/- Fails if any headline theorem depends on `sorryAx` or a non-standard axiom. -/
import Paper
open LSys

/-- info: 'LSys.infer_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms infer_complete
/-- info: 'LSys.infer_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms infer_sound
/-- info: 'LSys.infer_complete_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms infer_complete_fuel
/-- info: 'LSys.sharp_implies_insertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sharp_implies_insertion
/-- info: 'LSys.sharp_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sharp_witness
/-- info: 'LSys.exists_incompressible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exists_incompressible
/-- info: 'LSys.crit_of_insertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crit_of_insertion
/-- info: 'LSys.insertion_of_crit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms insertion_of_crit
/-- info: 'LSys.unary_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unary_iff
/-- info: 'LSys.conjC_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conjC_false
/-- info: 'LSys.identity_free_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms identity_free_expansion
/-- info: 'LSys.insertion_min_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms insertion_min_axiom
/-- info: 'LSys.insertion_min_dsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms insertion_min_dsize
/-- info: 'LSys.insP_pos_iff_crit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms insP_pos_iff_crit
/-- info: 'LSys.exists_incompressible_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exists_incompressible_log
/-- info: 'LSys.descCount_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descCount_closed
