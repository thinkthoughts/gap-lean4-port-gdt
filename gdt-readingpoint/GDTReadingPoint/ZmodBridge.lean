import GDTReadingPoint.Admissible
import Gap.Library.Zmodnz

namespace GDTReadingPoint

/--
GDT admissibility at the stored GAP residue is exactly the abstract
multiplicative-unit predicate in `ZModnZObj d`.
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

/--
Raw GDT residue `a : ℕ` enters the GAP representation through `ofNat`.

Reduction modulo `d` preserves coprimality with `d`, so GDT admissibility
is equivalent to the canonical GAP residue being a unit.
-/
theorem admissible_iff_isUnit_ofNat
    (a d : ℕ) [NeZero d] :
    Admissible a d ↔
      IsUnit (GAP.ZModnZObj.ofNat a : GAP.ZModnZObj d) := by
  rw [Admissible, GAP.ZModnZObj.isUnit_iff]
  change a.Coprime d ↔ (a % d).Coprime d
  exact (ZMod.coprime_mod_iff_coprime a d).symm

/--
Executable raw-residue form of the GDT ↔ GAP bridge.
-/
theorem admissible_iff_isUnitExec_ofNat
    (a d : ℕ) [NeZero d] :
    Admissible a d ↔
      GAP.ZModnZObj.isUnitExec
        (GAP.ZModnZObj.ofNat a : GAP.ZModnZObj d) = true := by
  rw [Admissible, GAP.ZModnZObj.isUnitExec_iff_coprime]
  change a.Coprime d ↔ (a % d).Coprime d
  exact (ZMod.coprime_mod_iff_coprime a d).symm

end GDTReadingPoint
