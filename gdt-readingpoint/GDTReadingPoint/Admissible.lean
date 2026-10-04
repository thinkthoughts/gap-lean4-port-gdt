import GDTReadingPoint.Basic

namespace GDTReadingPoint

/--
GDT admissibility at the divisor-reading point `d`.

This is the Lean-native form of `gcd(a,d)=1`.
-/
def Admissible (a d : ℕ) : Prop :=
  Nat.Coprime a d

/--
Complementary non-admissibility predicate.
-/
def NonAdmissible (a d : ℕ) : Prop :=
  ¬ Admissible a d

theorem admissible_iff_coprime (a d : ℕ) :
    Admissible a d ↔ Nat.Coprime a d := by
  rfl

end GDTReadingPoint
