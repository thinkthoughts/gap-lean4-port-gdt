namespace GDTReadingPoint

/--
Input parameters for the General Divisor Theorem reading point.

The positivity hypotheses follow the mathematical specification:
`N > 0` and `m > 0`.
-/
structure Params where
  N : ℕ
  m : ℕ
  a : ℕ
  hN : 0 < N
  hm : 0 < m

/--
`d = rad(gcd(m,N))`.

The exact `Nat.radical` API/import required by the host project should be
confirmed before uncommenting the executable definition below.
-/

/-
def d (p : Params) : ℕ :=
  Nat.radical (Nat.gcd p.m p.N)
-/

/--
`R = rad(N) / d`.
-/

/-
def R (p : Params) : ℕ :=
  Nat.radical p.N / d p
-/

/--
The GDT minimal-period target: `Tmin = m * R`.
-/

/-
def Tmin (p : Params) : ℕ :=
  p.m * R p
-/

end GDTReadingPoint
