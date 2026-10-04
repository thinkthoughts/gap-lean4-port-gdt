import Mathlib.Data.Nat.Factorization.Basic
import GDTReadingPoint.Basic

namespace GDTReadingPoint
namespace Params

/-- `rad(N)`, represented computationally as the product of prime divisors. -/
def radN (P : GDTReadingPoint.Params) : Nat :=
  ∏ q ∈ Nat.primeFactors P.N, q

/--
`d = rad(gcd(m,N))`, represented as the product of primes shared by
`N` and `m`.
-/
def d (P : GDTReadingPoint.Params) : Nat :=
  ∏ q ∈ Nat.primeFactors P.N ∩ Nat.primeFactors P.m, q

/--
`R`: the radical contribution from primes dividing `N` but not `m`.
-/
def R (P : GDTReadingPoint.Params) : Nat :=
  ∏ q ∈ Nat.primeFactors P.N \ Nat.primeFactors P.m, q

/-- `Tmin = mR`. -/
def Tmin (P : GDTReadingPoint.Params) : Nat :=
  P.m * R P

/--
The shared-prime and complementary-prime factors partition `radN`.
-/
theorem d_mul_R (P : GDTReadingPoint.Params) :
    d P * R P = radN P := by
  unfold d R radN
  exact Finset.prod_inter_mul_prod_diff _ _ _

end Params
end GDTReadingPoint
