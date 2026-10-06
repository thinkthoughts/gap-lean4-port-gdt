import GDTReadingPoint.Correction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Correction factor `C(N, m) = d / φ(d)` (review proposal)

Strategy: do all the arithmetic in `ℕ` as cross-multiplied identities,
then make a single, purely algebraic step into `ℚ`.

1. Exponent-blindness (PDF Lemma 2.1), in `ℕ`:
   `φ(k) * rad(k) = k * φ(rad(k))`.
   From Mathlib's `Nat.totient_mul_prod_primeFactors` applied to `k`
   and to `rad k` (whose prime factors are those of `k`).
2. Correction in `ℕ`: `φ(R) * φ(d) * N = d * R * φ(N)`.
   This is (1) at `k = N` combined with `rad N = d * R` and
   `φ(rad N) = φ(d) φ(R)`.
3. A cast-free ℚ lemma over abstract nonzero reals closes the target.
-/

namespace GDTReadingPoint

/-- `rad k` as used throughout the repo. -/
abbrev rad (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p

/-- `φ(rad k) = ∏_{p ∣ k} (p - 1)`. -/
theorem totient_rad (k : ℕ) :
    Nat.totient (rad k) = ∏ p ∈ k.primeFactors, (p - 1) := by
  have hprime : ∀ p ∈ k.primeFactors, p.Prime :=
    fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < rad k := Finset.prod_pos fun p hp => (hprime p hp).pos
  have h := Nat.totient_mul_prod_primeFactors (rad k)
  rw [Nat.primeFactors_prod hprime, Nat.mul_comm (rad k)] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

/-- PDF Lemma 2.1 (exponent-blindness), cross-multiplied in `ℕ`:
`k / φ(k) = rad(k) / φ(rad(k))`. Holds for every `k`, including `0`. -/
theorem totient_mul_rad (k : ℕ) :
    Nat.totient k * rad k = k * Nat.totient (rad k) := by
  rw [totient_rad]
  exact Nat.totient_mul_prod_primeFactors k

/-- PDF Lemma 2.1 in its literal ratio form (for `k ≥ 1`). -/
theorem div_totient_eq_rad (k : ℕ) (hk : 0 < k) :
    (k : ℚ) / Nat.totient k = (rad k : ℚ) / Nat.totient (rad k) := by
  have hφk : (Nat.totient k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  have hφr : (Nat.totient (rad k) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr
      (Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)).ne'
  rw [div_eq_div_iff hφk hφr]
  exact_mod_cast (totient_mul_rad k).symm.trans (Nat.mul_comm _ _)

/-- Correction identity in `ℕ`: `φ(R) φ(d) N = d R φ(N)`. -/
theorem correction_nat (P : Params) :
    Nat.totient (Params.R P) * Nat.totient (Params.d P) * P.N =
      Params.d P * Params.R P * Nat.totient P.N := by
  have hb := totient_mul_rad P.N
  have hrad : rad P.N = Params.radN P := rfl
  rw [hrad, totient_radN_eq_mul, ← Params.d_mul_R P] at hb
  calc Nat.totient (Params.R P) * Nat.totient (Params.d P) * P.N
      = P.N * (Nat.totient (Params.d P) * Nat.totient (Params.R P)) := by ring
    _ = Nat.totient P.N * (Params.d P * Params.R P) := hb.symm
    _ = Params.d P * Params.R P * Nat.totient P.N := by ring

/-- The naive independent-density prediction `φ(N) / (N m)`. -/
def naiveDensity (P : Params) : ℚ :=
  (Nat.totient P.N : ℚ) / ((P.N : ℚ) * (P.m : ℚ))

/-- Pure field algebra, no casts: the only step that happens in `ℚ`. -/
theorem correction_field_step {K : Type*} [Field K]
    {φR φd N d R m φN : K}
    (hφd : φd ≠ 0) (hN : N ≠ 0) (hR : R ≠ 0) (hm : m ≠ 0)
    (h : φR * φd * N = d * R * φN) :
    φR / (m * R) = d / φd * (φN / (N * m)) := by
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hm hR)
    (mul_ne_zero hφd (mul_ne_zero hN hm))]
  linear_combination m * h

/-- PDF Theorem 3, ratio: `density = C(N,m) · naive`, `C = d / φ(d)`. -/
theorem density_eq_correctionFactor_mul_naive (P : Params) :
    density P = correctionFactor P * naiveDensity P := by
  have hφd : (Nat.totient (Params.d P) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr
      (Finset.prod_pos fun _ hq =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1).pos)).ne'
  have hR : (Params.R P : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun _ hq =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos).ne'
  have hN : (P.N : ℚ) ≠ 0 := by exact_mod_cast P.hN.ne'
  have hm : (P.m : ℚ) ≠ 0 := by exact_mod_cast P.hm.ne'
  have h : (Nat.totient (Params.R P) : ℚ) * Nat.totient (Params.d P) * P.N =
      Params.d P * Params.R P * Nat.totient P.N := by
    exact_mod_cast correction_nat P
  unfold density correctionFactor naiveDensity Params.Tmin
  push_cast
  exact correction_field_step hφd hN hR hm h

/-- Equivalent "density ratio" form used in the PDF. -/
theorem density_div_naive_eq_correctionFactor (P : Params) :
    density P / naiveDensity P = correctionFactor P := by
  have hnaive : naiveDensity P ≠ 0 := by
    unfold naiveDensity
    have h1 : (Nat.totient P.N : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr P.hN).ne'
    have h2 : (P.N : ℚ) ≠ 0 := by exact_mod_cast P.hN.ne'
    have h3 : (P.m : ℚ) ≠ 0 := by exact_mod_cast P.hm.ne'
    exact div_ne_zero h1 (mul_ne_zero h2 h3)
  rw [density_eq_correctionFactor_mul_naive, mul_div_assoc, div_self hnaive, mul_one]

end GDTReadingPoint
