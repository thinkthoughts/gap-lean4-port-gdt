import GDTReadingPoint.Admissible
import RequestProject.Gap.Library.Zmodnz

namespace GDTReadingPoint

/--
GDT admissibility at the stored GAP residue is exactly the abstract
multiplicative-unit predicate in `ZModnZObj d`.

This is the first GAP ↔ GDT bridge:
`gcd(a.val, d) = 1` ↔ `a` is a unit modulo `d`.
-/
theorem admissible_iff_isUnit
    {d : ℕ} [NeZero d]
    (a : GAP.ZModnZObj d) :
    Admissible a.val d ↔ IsUnit a := by
  simpa [Admissible] using (GAP.ZModnZObj.isUnit_iff a).symm

/--
Executable form of the same bridge, using GAP's verified `isUnitExec`.
-/
theorem admissible_iff_isUnitExec
    {d : ℕ} [NeZero d]
    (a : GAP.ZModnZObj d) :
    Admissible a.val d ↔ GAP.ZModnZObj.isUnitExec a = true := by
  simpa [Admissible] using
    (GAP.ZModnZObj.isUnitExec_iff_coprime a).symm

end GDTReadingPoint
