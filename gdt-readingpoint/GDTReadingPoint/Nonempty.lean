import Mathlib.Data.Nat.ModEq
import GDTReadingPoint.Admissible
import GDTReadingPoint.Good

namespace GDTReadingPoint

/--
If the GDT residue class is admissible, the conditioned set is nonempty.

The witness is obtained by the Chinese remainder theorem from

* `n ≡ a (mod m)`, and
* `n ≡ 1 (mod R)`,

using `Coprime m R`.
-/
theorem exists_good_of_admissible
    (P : Params)
    (hadm : Admissible P.a (Params.d P)) :
    ∃ n, Good P n := by

  let x :=
    Nat.chineseRemainder
      (Params.coprime_m_R P)
      P.a
      1

  refine ⟨x.1, ?_⟩
  constructor

  · exact x.2.1

  · have hmod_d :
        Nat.ModEq (Params.d P) x.1 P.a :=
      x.2.1.of_dvd (Params.d_dvd_m P)

    have hcop_d :
        Nat.Coprime x.1 (Params.d P) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      rw [hmod_d.gcd_eq]
      exact hadm.gcd_eq_one

    have hmod_R :
        Nat.ModEq (Params.R P) x.1 1 :=
      x.2.2

    have hcop_R :
        Nat.Coprime x.1 (Params.R P) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      rw [hmod_R.gcd_eq]
      simp

    have hcop_radN :
        Nat.Coprime x.1 (Params.radN P) := by
      rw [← Params.d_mul_R P]
      exact hcop_d.mul_right hcop_R

    exact
      (Params.coprime_radN_iff P x.1).1 hcop_radN

end GDTReadingPoint
