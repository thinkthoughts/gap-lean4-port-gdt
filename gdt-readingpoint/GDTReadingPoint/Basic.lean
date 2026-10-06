namespace GDTReadingPoint

/--
Input parameters for the General Divisor Theorem reading point.

The positivity hypotheses follow the mathematical specification:
`N > 0` and `m > 0`.

The fields are written `Nat` (not `ℕ`): this file imports nothing, so the
Mathlib notation `ℕ` is unavailable here, and with `autoImplicit` it would be
silently auto-bound as a type variable, making `Params` uninhabited.
-/
structure Params where
  N : Nat
  m : Nat
  a : Nat
  hN : 0 < N
  hm : 0 < m

-- The GDT quantities `d`, `R`, `Tmin` are defined in `Parameters.lean`.

end GDTReadingPoint
