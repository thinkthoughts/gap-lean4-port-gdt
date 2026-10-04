import Mathlib.Data.Nat.ModEq
import GDTReadingPoint.Good

namespace GDTReadingPoint

/--
The modulus `m` divides the proposed GDT period `Tmin = mR`.
-/
theorem m_dvd_Tmin (P : Params) :
    P.m ∣ Params.Tmin P := by
  unfold Params.Tmin
  exact dvd_mul_right P.m (Params.R P)

/--
Translation by `Tmin` preserves membership in the GDT-conditioned set.

This periodicity statement is unconditional: admissibility controls the
empty/nonempty branch and later minimality/count statements, but translation
by the full period preserves membership for every residue class.
-/
theorem good_add_Tmin_iff
    (P : Params) (n : Nat) :
    Good P (n + Params.Tmin P) ↔ Good P n := by

  have hmod_m :
      Nat.ModEq P.m (n + Params.Tmin P) n := by
    unfold Nat.ModEq
    rcases m_dvd_Tmin P with ⟨k, hk⟩
    rw [hk]
    simp [Nat.add_mod]

  have hmod_rad :
      Nat.ModEq (Params.radN P) (n + Params.Tmin P) n := by
    unfold Nat.ModEq
    rcases Params.radN_dvd_Tmin P with ⟨k, hk⟩
    rw [hk]
    simp [Nat.add_mod]

  constructor

  · rintro ⟨hres, hcop⟩
    constructor

    · change Nat.ModEq P.m n P.a
      change Nat.ModEq P.m (n + Params.Tmin P) P.a at hres
      exact hmod_m.symm.trans hres

    · have hshiftRad :
          Nat.Coprime (n + Params.Tmin P) (Params.radN P) :=
        (Params.coprime_radN_iff P (n + Params.Tmin P)).2 hcop

      have hgcd :
          Nat.gcd n (Params.radN P) = 1 := by
        rw [← hmod_rad.gcd_eq]
        exact hshiftRad.gcd_eq_one

      have hnRad :
          Nat.Coprime n (Params.radN P) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact hgcd

      exact (Params.coprime_radN_iff P n).1 hnRad

  · rintro ⟨hres, hcop⟩
    constructor

    · change Nat.ModEq P.m (n + Params.Tmin P) P.a
      change Nat.ModEq P.m n P.a at hres
      exact hmod_m.trans hres

    · have hnRad :
          Nat.Coprime n (Params.radN P) :=
        (Params.coprime_radN_iff P n).2 hcop

      have hgcd :
          Nat.gcd (n + Params.Tmin P) (Params.radN P) = 1 := by
        rw [hmod_rad.gcd_eq]
        exact hnRad.gcd_eq_one

      have hshiftRad :
          Nat.Coprime (n + Params.Tmin P) (Params.radN P) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact hgcd

      exact
        (Params.coprime_radN_iff P (n + Params.Tmin P)).1 hshiftRad

end GDTReadingPoint
