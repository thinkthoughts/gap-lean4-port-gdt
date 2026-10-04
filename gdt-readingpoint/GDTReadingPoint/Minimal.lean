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

end GDTReadingPoint
