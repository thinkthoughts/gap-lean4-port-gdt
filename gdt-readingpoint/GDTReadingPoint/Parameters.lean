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

/--
`m` is coprime to the complementary radical factor `R`.

Every prime appearing in `R` divides `N` but is excluded from the
prime support of `m`.
-/
theorem coprime_m_R (P : GDTReadingPoint.Params) :
    Nat.Coprime P.m (R P) := by
  unfold R
  apply Nat.Coprime.prod_right
  intro q hq
  have hq' := Finset.mem_sdiff.mp hq
  have hqN : q ∈ Nat.primeFactors P.N := hq'.1
  have hqnotm : q ∉ Nat.primeFactors P.m := hq'.2
  have hqprime : Nat.Prime q :=
    Nat.prime_of_mem_primeFactors hqN
  rw [Nat.Prime.coprime_iff_not_dvd hqprime]
  intro hqdvd
  apply hqnotm
  exact Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd, P.hm.ne'⟩

end Params
end GDTReadingPoint
