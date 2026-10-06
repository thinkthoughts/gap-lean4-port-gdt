import GDTReadingPoint.Admissible

namespace GDTReadingPoint

/--
Regression guard: `Params` must be inhabited. If a field type is ever
auto-bound (e.g. `ℕ` without its notation in scope), this stops compiling.
-/
example : Params := ⟨18, 2, 1, by decide, by decide⟩

/--
A minimal arithmetic reading point: residue `1` is admissible modulo `30`.
-/
example : Admissible 1 30 := by
  unfold Admissible; decide

/--
A non-admissible arithmetic reading point: residue `3` is not coprime to `30`.
-/
example : NonAdmissible 3 30 := by
  unfold NonAdmissible Admissible; decide

end GDTReadingPoint
