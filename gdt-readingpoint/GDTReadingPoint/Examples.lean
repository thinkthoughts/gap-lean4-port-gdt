import GDTReadingPoint.Admissible

namespace GDTReadingPoint

/--
A minimal arithmetic reading point: residue `1` is admissible modulo `30`.
-/
example : Admissible 1 30 := by
  decide

/--
A non-admissible arithmetic reading point: residue `3` is not coprime to `30`.
-/
example : NonAdmissible 3 30 := by
  decide

end GDTReadingPoint
