import Mathlib.Data.Nat.Factorization.Basic
import GDTReadingPoint.Basic

namespace GDTReadingPoint
namespace Params

variable (P : Params)

/-- `rad(N)`, represented computationally as the product of prime divisors. -/
def radN : Nat :=
  ∏ q ∈ P.N.primeFactors, q

/--
`d = rad(gcd(m,N))`, represented as the product of primes shared by
`N` and `m`.
-/
def d : Nat :=
  ∏ q ∈ P.N.primeFactors ∩ P.m.primeFactors, q

/--
`R`: the radical contribution from primes dividing `N` but not `m`.
This is the prime-set form described in the GDT specification.
-/
def R : Nat :=
  ∏ q ∈ P.N.primeFactors \ P.m.primeFactors, q

/-- `Tmin = mR`. -/
def Tmin : Nat :=
  P.m * P.R

/--
The shared-prime and complementary-prime factors partition `radN`.
-/
theorem d_mul_R : P.d * P.R = P.radN := by
  unfold d R radN
  exact Finset.prod_inter_mul_prod_diff _ _ _

end Params
end GDTReadingPoint
