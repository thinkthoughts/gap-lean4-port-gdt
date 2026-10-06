import GDTReadingPoint.Count
open GDTReadingPoint

/-- `Params` has no inhabitants: its `N` field must produce an element of `Empty`. -/
theorem params_empty (P : Params) : False := (@Params.N P Empty).elim

/-- Hence any statement about the GDT objects is provable, e.g. a false count. -/
example (P : Params) (hadm : Admissible P.a (Params.d P)) (k : Nat) :
    goodCount P k = Nat.totient (Params.R P) + 1 := (params_empty P).elim

#print axioms params_empty
