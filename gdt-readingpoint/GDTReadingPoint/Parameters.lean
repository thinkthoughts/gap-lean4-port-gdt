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
Prime support contributing to `R`: primes dividing `N` but not `m`.
-/
def Rset (P : GDTReadingPoint.Params) : Finset Nat :=
  Nat.primeFactors P.N \ Nat.primeFactors P.m

/--
`R`: the radical contribution from primes dividing `N` but not `m`.
-/
def R (P : GDTReadingPoint.Params) : Nat :=
  ∏ q ∈ Rset P, q

/--
`Rrest`: the complementary factor after removing one prime `q`
from the prime support of `R`.
-/
def Rrest (P : GDTReadingPoint.Params) (q : Nat) : Nat :=
  ∏ p ∈ (Rset P).erase q, p

/-- `Tmin = mR`. -/
def Tmin (P : GDTReadingPoint.Params) : Nat :=
  P.m * R P

/--
The shared-prime and complementary-prime factors partition `radN`.
-/
theorem d_mul_R (P : GDTReadingPoint.Params) :
    d P * R P = radN P := by
  unfold d R Rset radN
  exact Finset.prod_inter_mul_prod_diff _ _ _

/--
If `q` belongs to the prime support of `R`, then
`R = q * Rrest`.
-/
theorem R_eq_q_mul_Rrest
    (P : GDTReadingPoint.Params)
    {q : Nat}
    (hq : q ∈ Rset P) :
    R P = q * Rrest P q := by
  unfold R Rrest
  rw [← Finset.prod_erase_mul _ _ hq]
  ac_rfl

/--
`m` is coprime to the complementary radical factor `R`.

Every prime appearing in `R` divides `N` but is excluded from the
prime support of `m`.
-/
theorem coprime_m_R (P : GDTReadingPoint.Params) :
    Nat.Coprime P.m (R P) := by
  have hm0 : P.m ≠ 0 := Nat.ne_of_gt P.hm

  have hRpos : 0 < R P := by
    unfold R Rset
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
    unfold R Rset
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
The shared radical factor `d` also divides `N`.
-/
theorem d_dvd_N (P : GDTReadingPoint.Params) :
    d P ∣ P.N := by
  have hN0 : P.N ≠ 0 := Nat.ne_of_gt P.hN
  have hm0 : P.m ≠ 0 := Nat.ne_of_gt P.hm
  unfold d
  rw [← Nat.primeFactors_gcd hN0 hm0]
  exact dvd_trans
    (Nat.prod_primeFactors_dvd (Nat.gcd P.N P.m))
    (Nat.gcd_dvd_left P.N P.m)

/--
The radical of `N` divides the proposed period `Tmin = mR`.
-/
theorem radN_dvd_Tmin (P : GDTReadingPoint.Params) :
    radN P ∣ Tmin P := by
  rw [← d_mul_R P]
  rcases d_dvd_m P with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold Tmin
  rw [hk]
  ac_rfl

/--
Coprimality with `N` is equivalent to coprimality with its radical support.

Only the prime support of `N` matters for the GDT coprimality condition.
-/
theorem coprime_radN_iff
    (P : GDTReadingPoint.Params) (n : Nat) :
    Nat.Coprime n (radN P) ↔ Nat.Coprime n P.N := by
  constructor

  · intro hrad
    apply Nat.coprime_of_dvd
    intro q hqprime hqdivn hqdivN

    have hN0 : P.N ≠ 0 := Nat.ne_of_gt P.hN

    have hqmemN : q ∈ Nat.primeFactors P.N := by
      exact Nat.mem_primeFactors.mpr
        ⟨hqprime, hqdivN, hN0⟩

    have hqdivRad : q ∣ radN P := by
      unfold radN
      exact Finset.dvd_prod_of_mem _ hqmemN

    have hqcop : Nat.Coprime q (radN P) :=
      hrad.of_dvd_left hqdivn

    exact
      (hqprime.coprime_iff_not_dvd.mp hqcop) hqdivRad

  · intro hN
    apply hN.of_dvd_right
    unfold radN
    exact Nat.prod_primeFactors_dvd P.N

/--
A prime `q` in `Rset` is coprime to the complementary factor `Rrest`.
-/
theorem coprime_q_Rrest
    (P : GDTReadingPoint.Params)
    {q : Nat}
    (hq : q ∈ Rset P) :
    Nat.Coprime q (Rrest P q) := by
  have hqprime : Nat.Prime q := by
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hq).1

  unfold Rrest
  rw [Nat.coprime_prod_right_iff]

  intro p hp

  have hpRset : p ∈ Rset P :=
    Finset.mem_of_mem_erase hp

  have hpprime : Nat.Prime p := by
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hpRset).1

  have hpne : p ≠ q :=
    Finset.ne_of_mem_erase hp

  rw [hqprime.coprime_iff_not_dvd]

  intro hqp
  have hpeq : p = q := by
    exact (Nat.dvd_prime hpprime).mp hqp |>.resolve_left hqprime.ne_one |>.symm

  exact hpne hpeq

end Params
end GDTReadingPoint
