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

-- Planned GDT quantities:
--
-- d     = rad(gcd(m,N))
-- R     = rad(N) / d
-- Tmin  = m * R
--
-- We add these only after confirming the exact radical API
-- available in the host Mathlib version.

end GDTReadingPoint
