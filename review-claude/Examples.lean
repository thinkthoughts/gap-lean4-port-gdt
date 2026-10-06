import Review.Conformance
import Review.Correction
import Mathlib.Tactic.Simproc.Factors
import Mathlib.Tactic.NormNum

/-!
# The two distinguishing examples of `gdt.pdf` §3.3 (review proposal)

All checks are kernel-checked with `decide`/`simp`; no `native_decide`.
-/

namespace GDTReadingPoint.Examples

/-- §3.3 (i): `N = 18, m = 2, a = 1`. -/
def P18 : Params := ⟨18, 2, 1, by decide, by decide⟩

theorem pf18 : Nat.primeFactors 18 = {2, 3} := by
  simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]

theorem pf2 : Nat.primeFactors 2 = {2} := Nat.Prime.primeFactors Nat.prime_two

theorem P18_d : Params.d P18 = 2 := by
  simp [Params.d, P18, pf18, pf2]

theorem P18_R : Params.R P18 = 3 := by
  simp only [Params.R, Params.Rset, P18, pf18, pf2]; decide

/-- Exact minimal period is `6`, not `N = 18`. -/
theorem P18_Tmin : Params.Tmin P18 = 6 := by
  unfold Params.Tmin; rw [P18_R]; rfl

theorem P18_admissible : Admissible P18.a (Params.d P18) := by
  rw [P18_d]; unfold Admissible; decide

/-- `18` is a period (Theorem 1′), but the least positive period is `6`. -/
theorem P18_18_period_not_minimal :
    IsPeriod P18 18 ∧ IsLeast {T | 0 < T ∧ IsPeriod P18 T} 6 := by
  refine ⟨?_, P18_Tmin ▸ Tmin_isLeast P18 P18_admissible⟩
  intro n
  have h := (good_periodic P18).nat_mul 3 n
  rw [P18_Tmin] at h
  exact iff_of_eq h

/-- `{1,5,7,11,13,17}` in `[1,18]`: count `6 = φ(9)`. -/
theorem P18_S18 : S P18 18 = 6 := by decide

/-- §3.3 (ii): `N = 5, m = 6, a = 2` — admissible although `gcd(a,m) = 2`. -/
def P5 : Params := ⟨5, 6, 2, by decide, by decide⟩

theorem pf5 : Nat.primeFactors 5 = {5} := Nat.Prime.primeFactors (by norm_num)

theorem pf6 : Nat.primeFactors 6 = {2, 3} := by
  simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]

theorem P5_d : Params.d P5 = 1 := by
  simp [Params.d, P5, pf5, pf6]

theorem P5_R : Params.R P5 = 5 := by
  simp only [Params.R, Params.Rset, P5, pf5, pf6]; decide

theorem P5_Tmin : Params.Tmin P5 = 30 := by
  unfold Params.Tmin; rw [P5_R]; rfl

theorem P5_admissible : Admissible P5.a (Params.d P5) := by
  rw [P5_d]; unfold Admissible; decide

theorem P5_not_coprime_a_m : ¬ Nat.Coprime P5.a P5.m := by decide

/-- `{2, 8, 14, 26}`: count `4 = φ(5)` in one period `[1, 30]`. -/
theorem P5_S30 : S P5 30 = 4 := by decide

theorem P5_correction : correctionFactor P5 = 1 := by
  simp [correctionFactor, P5_d]

/-- The wrong `m/φ(m)` prediction would give `3`. -/
theorem P5_wrong_factor : (P5.m : ℚ) / Nat.totient P5.m = 3 := by
  rw [show P5.m = 6 from rfl, show Nat.totient 6 = 2 by decide]; norm_num

end GDTReadingPoint.Examples
