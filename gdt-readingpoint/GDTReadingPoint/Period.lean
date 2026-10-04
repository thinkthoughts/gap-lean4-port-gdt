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

This periodicity statement is unconditional: admissibility is needed for
the empty/nonempty dichotomy and later minimality/count statements, but not
for preservation of membership under a full period shift.
-/
theorem good_add_Tmin_iff
    (P : Params) (n : Nat) :
    Good P (n + Params.Tmin P) ↔ Good P n := by
  constructor

  · intro h
    constructor

    · have hm : P.m ∣ Params.Tmin P :=
        m_dvd_Tmin P
      rcases hm with ⟨k, hk⟩
      unfold Good at h ⊢
      dsimp at h ⊢
      rw [hk] at h
      simpa [Nat.add_mod] using h.1

    · have hrad :
          Nat.Coprime (n + Params.Tmin P) (Params.radN P) := by
        exact (Params.coprime_radN_iff P (n + Params.Tmin P)).2 h.2

      have hmod :
          (n + Params.Tmin P) % Params.radN P =
            n % Params.radN P := by
        rcases Params.radN_dvd_Tmin P with ⟨k, hk⟩
        rw [hk]
        simp [Nat.add_mod]

      have hnrad : Nat.Coprime n (Params.radN P) := by
        rw [Nat.coprime_comm] at hrad ⊢
        rw [Nat.coprime_comm]
        simpa [hmod] using hrad

      exact (Params.coprime_radN_iff P n).1 hnrad

  · intro h
    constructor

    · have hm : P.m ∣ Params.Tmin P :=
        m_dvd_Tmin P
      rcases hm with ⟨k, hk⟩
      unfold Good at h ⊢
      dsimp at h ⊢
      rw [hk]
      simpa [Nat.add_mod] using h.1

    · have hnrad :
          Nat.Coprime n (Params.radN P) :=
        (Params.coprime_radN_iff P n).2 h.2

      have hmod :
          (n + Params.Tmin P) % Params.radN P =
            n % Params.radN P := by
        rcases Params.radN_dvd_Tmin P with ⟨k, hk⟩
        rw [hk]
        simp [Nat.add_mod]

      have hshift :
          Nat.Coprime (n + Params.Tmin P) (Params.radN P) := by
        rw [Nat.coprime_comm] at hnrad ⊢
        rw [Nat.coprime_comm]
        simpa [hmod] using hnrad

      exact
        (Params.coprime_radN_iff P (n + Params.Tmin P)).1 hshift

end GDTReadingPoint
