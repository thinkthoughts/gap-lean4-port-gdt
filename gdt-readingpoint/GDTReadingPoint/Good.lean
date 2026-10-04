import GDTReadingPoint.Parameters

namespace GDTReadingPoint

/--
The GDT-conditioned set:
`n` lies in the residue class `a mod m` and is coprime to `N`.
-/
def Good (P : Params) (n : Nat) : Prop :=
  n % P.m = P.a % P.m ∧ Nat.Coprime n P.N

end GDTReadingPoint
