import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
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
  have hm0 : P.m ≠ 0 := Nat.ne_of_gt P.hm

  have hRpos : 0 < R P := by
    unfold R
    apply Finset.prod_pos
    intro q hq
    have hqN :
        q ∈ Nat.primeFactors P.N :=
      (Finset.mem_sdiff.mp hq).1
    exact (Nat.prime_of_mem_primeFactors hqN).pos

  have hR0 : R P ≠ 0 := Nat.ne_of_gt hRpos

  apply (Nat.disjoint_primeFactors hm0 hR0).mp

  have hpfR :
      Nat.primeFactors (R P) =
        Nat.primeFactors P.N \ Nat.primeFactors P.m := by
    unfold R
    apply Nat.primeFactors_prod
    intro q hq
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hq).1

  rw [hpfR]
  rw [Finset.disjoint_left]
  intro q hqm hqR
  exact (Finset.mem_sdiff.mp hqR).2 hqm

/--
The shared radical factor `d` divides `m`.
-/
theorem d_dvd_m (P : GDTReadingPoint.Params) :
    d P ∣ P.m := by
  have hN0 : P.N ≠ 0 := Nat.ne_of_gt P.hN
  have hm0 : P.m ≠ 0 := Nat.ne_of_gt P.hm
  unfold d
  rw [← Nat.primeFactors_gcd hN0 hm0]
  exact dvd_trans
    (Nat.prod_primeFactors_dvd (Nat.gcd P.N P.m))
    (Nat.gcd_dvd_right P.N P.m)

/--
The radical of `N` divides the proposed period `Tmin = mR`.

This is the structural fact that will make GDT membership invariant
under translation by `Tmin`.
-/
theorem radN_dvd_Tmin (P : GDTReadingPoint.Params) :
    radN P ∣ Tmin P := by
  rw [← d_mul_R P]
  rcases d_dvd_m P with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold Tmin
  rw [hk]
  ac_rfl

end Params
end GDTReadingPoint
