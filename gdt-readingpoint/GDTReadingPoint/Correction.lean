import GDTReadingPoint.Density

namespace GDTReadingPoint

/--
Euler's totient is multiplicative across the coprime factorization
`radN = d * R`.
-/
theorem totient_radN_eq_mul
    (P : Params) :
    Nat.totient (Params.radN P) =
      Nat.totient (Params.d P) *
        Nat.totient (Params.R P) := by
  rw [← Params.d_mul_R P]
  exact Nat.totient_mul (Params.coprime_d_R P)

/--
The GDT correction factor.
-/
def correctionFactor (P : Params) : ℚ :=
  (Params.d P : ℚ) /
    (Nat.totient (Params.d P) : ℚ)

/--
The admissible GDT density equals the naive residue-class density
times the exact correction factor `d / φ(d)`.
-/
theorem density_eq_correction_mul_baseline
    (P : Params) :
    density P =
      correctionFactor P *
        (
          ((1 : ℚ) / (P.m : ℚ)) *
          ((Nat.totient (Params.radN P) : ℚ) /
            (Params.radN P : ℚ))
        ) := by
  unfold density correctionFactor Params.Tmin
  rw [totient_radN_eq_mul P]
  rw [← Params.d_mul_R P]

  have hRpos : 0 < Params.R P := by
    unfold Params.R Params.Rset
    apply Finset.prod_pos
    intro q hq
    exact
      (Nat.prime_of_mem_primeFactors
        (Finset.mem_sdiff.mp hq).1).pos

  have hdpos : 0 < Params.d P := by
    unfold Params.d
    apply Finset.prod_pos
    intro q hq
    exact
      (Nat.prime_of_mem_primeFactors
        (Finset.mem_inter.mp hq).1).pos

  have hphidpos :
      0 < Nat.totient (Params.d P) := by
    exact Nat.totient_pos.mpr hdpos

  have hm0 : (P.m : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (P.m : ℚ) := by
      exact_mod_cast P.hm
    exact ne_of_gt h

  have hR0 : (Params.R P : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (Params.R P : ℚ) := by
      exact_mod_cast hRpos
    exact ne_of_gt h

  have hd0 : (Params.d P : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (Params.d P : ℚ) := by
      exact_mod_cast hdpos
    exact ne_of_gt h

  have hphid0 :
      (Nat.totient (Params.d P) : ℚ) ≠ 0 := by
    have h :
        (0 : ℚ) <
          (Nat.totient (Params.d P) : ℚ) := by
      exact_mod_cast hphidpos
    exact ne_of_gt h

  norm_num only [Nat.cast_mul]
  field_simp [hm0, hR0, hd0, hphid0]
  ring

end GDTReadingPoint
