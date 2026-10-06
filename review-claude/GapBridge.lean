import Review.ZmodnzLocal
import Review.CountAlt
import Mathlib.Data.Nat.Totient

/-!
# Deeper GAP bridge (review proposal)

In the repo this file would `import RequestProject.Gap.Library.Zmodnz`;
`Review.ZmodnzLocal` is a body-identical scratch copy with narrowed imports.

Goal: state the GDT objects in GAP's `ZModnZObj`, so that the GAP side is
load-bearing in the statements rather than a leaf adapter.
-/

namespace GDTReadingPoint
open GAP

/-- `ofNat` equality is congruence. -/
theorem ofNat_eq_ofNat_iff {n : ℕ} [NeZero n] (x y : ℕ) :
    (ZModnZObj.ofNat x : ZModnZObj n) = ZModnZObj.ofNat y ↔ x % n = y % n := by
  constructor
  · intro h; exact congrArg ZModnZObj.val h
  · intro h; exact ZModnZObj.ext h

/-- The GDT acceptance predicate, read entirely in GAP residue objects:
`n ≡ a (mod m)` in `ZModnZObj m`, and `n` a unit in `ZModnZObj N`. -/
theorem good_iff_gap (P : Params) (n : ℕ) :
    haveI : NeZero P.m := ⟨P.hm.ne'⟩
    haveI : NeZero P.N := ⟨P.hN.ne'⟩
    Good P n ↔
      (ZModnZObj.ofNat n : ZModnZObj P.m) = ZModnZObj.ofNat P.a ∧
        IsUnit (ZModnZObj.ofNat n : ZModnZObj P.N) := by
  haveI : NeZero P.m := ⟨P.hm.ne'⟩
  haveI : NeZero P.N := ⟨P.hN.ne'⟩
  rw [ofNat_eq_ofNat_iff, ZModnZObj.isUnit_iff]
  change _ ↔ _ ∧ (n % P.N).Coprime P.N
  rw [ZMod.coprime_mod_iff_coprime]
  rfl

/-- Executable form, using GAP's verified `isUnitExec`. -/
theorem good_iff_gap_exec (P : Params) (n : ℕ) :
    haveI : NeZero P.m := ⟨P.hm.ne'⟩
    haveI : NeZero P.N := ⟨P.hN.ne'⟩
    Good P n ↔
      (ZModnZObj.ofNat n : ZModnZObj P.m) = ZModnZObj.ofNat P.a ∧
        ZModnZObj.isUnitExec (ZModnZObj.ofNat n : ZModnZObj P.N) = true := by
  haveI : NeZero P.m := ⟨P.hm.ne'⟩
  haveI : NeZero P.N := ⟨P.hN.ne'⟩
  rw [good_iff_gap, ZModnZObj.isUnit_iff_isUnitExec]

/-- GAP's `ZModnZObj n` and Mathlib's `ZMod n` as rings. -/
def ZModnZObj.ringEquivZMod (n : ℕ) [NeZero n] : ZModnZObj n ≃+* ZMod n :=
  ZModnZObj.equivZMod.ringEquiv

/-- The unit group of GAP's `ℤ/nℤ` has `φ(n)` elements. -/
theorem card_units_ZModnZObj (n : ℕ) [NeZero n] :
    Fintype.card (ZModnZObj n)ˣ = Nat.totient n := by
  classical
  rw [Fintype.card_congr
      (Units.mapEquiv (ZModnZObj.ringEquivZMod n).toMulEquiv).toEquiv,
    ZMod.card_units_eq_totient]

/-- PDF RP3 in GAP form: per-period count = `|(ZModnZObj R)ˣ|`. -/
theorem goodCount_eq_card_units_gap
    (P : Params) (hadm : Admissible P.a (Params.d P)) (k : ℕ) :
    haveI : NeZero (Params.R P) := ⟨(Params.R_pos P).ne'⟩
    goodCount P k = Fintype.card (ZModnZObj (Params.R P))ˣ := by
  haveI : NeZero (Params.R P) := ⟨(Params.R_pos P).ne'⟩
  rw [card_units_ZModnZObj, goodCount_eq_totient_R' P hadm k]

end GDTReadingPoint
