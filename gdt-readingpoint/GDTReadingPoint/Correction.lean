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
  rw [Params.d_mul_R P]
  norm_num

end GDTReadingPoint
