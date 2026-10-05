import GDTReadingPoint.Count

namespace GDTReadingPoint

/--
The exact GDT density in the admissible branch:
`φ(R) / (mR)`.
-/
def density (P : Params) : ℚ :=
  (Nat.totient (Params.R P) : ℚ) /
    (Params.Tmin P : ℚ)

/--
The density expressed using the specified period `Tmin = mR`.
-/
theorem density_eq_totient_div_Tmin
    (P : Params) :
    density P =
      (Nat.totient (Params.R P) : ℚ) /
        (Params.Tmin P : ℚ) := by
  rfl

/--
The density expressed in the GDT form `φ(R) / (mR)`.
-/
theorem density_eq_totient_div_mR
    (P : Params) :
    density P =
      (Nat.totient (Params.R P) : ℚ) /
        ((P.m : ℚ) * (Params.R P : ℚ)) := by
  simp [density, Params.Tmin, Nat.cast_mul]

/--
For every admissible class and every period-length window,
the exact count divided by the window length equals the GDT density.
-/
theorem goodCount_div_Tmin_eq_density
    (P : Params)
    (hadm : Admissible P.a (Params.d P))
    (k : Nat) :
    (goodCount P k : ℚ) / (Params.Tmin P : ℚ) =
      density P := by
  rw [goodCount_eq_totient_R P hadm k]
  rfl

end GDTReadingPoint
