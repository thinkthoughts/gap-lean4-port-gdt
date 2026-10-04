import GDTReadingPoint.Nonempty
import GDTReadingPoint.Period

namespace GDTReadingPoint

/--
`T` is a period of the GDT-conditioned set if translation by `T`
preserves membership for every natural reading point.
-/
def IsPeriod (P : Params) (T : Nat) : Prop :=
  ∀ n, Good P (n + T) ↔ Good P n

/--
The specified GDT period `Tmin = mR` is a period of the conditioned set.
-/
theorem Tmin_isPeriod (P : Params) :
    IsPeriod P (Params.Tmin P) := by
  intro n
  exact good_add_Tmin_iff P n

/--
For an admissible GDT class, every period is divisible by `m`.
-/
theorem m_dvd_period
    (P : Params)
    (hadm : Admissible P.a (Params.d P))
    {T : Nat}
    (hT : IsPeriod P T) :
    P.m ∣ T := by
  rcases exists_good_of_admissible P hadm with ⟨n, hn⟩

  have hnT : Good P (n + T) :=
    (hT n).2 hn

  have hmod :
      Nat.ModEq P.m (n + T) n := by
    change Nat.ModEq P.m (n + T) P.a at hnT
    change Nat.ModEq P.m n P.a at hn
    exact hnT.1.trans hn.1.symm

  exact Nat.add_modEq_left_iff.mp hmod

end GDTReadingPoint
