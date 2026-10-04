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
  rw [Nat.coprime_comm]
  refine Nat.coprime_of_dvd' ?_
  intro q hqprime hqprod hqm
  have hqmem :
      q ∈ Nat.primeFactors P.N \ Nat.primeFactors P.m := by
    have hqmemProd :
        q ∈ Nat.primeFactors P.N \ Nat.primeFactors P.m := by
      simpa using
        (Finset.dvd_prod_iff_of_prime hqprime).mp hqprod
    exact hqmemProd
  have hqnotmem : q ∉ Nat.primeFactors P.m := hqmem.2
  have hqmemm : q ∈ Nat.primeFactors P.m := by
    exact Nat.mem_primeFactors.mpr ⟨hqprime, hqm, P.hm.ne'⟩
  exact False.elim (hqnotmem hqmemm)

end Params
end GDTReadingPoint
