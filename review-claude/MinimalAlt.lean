import GDTReadingPoint.Minimal
import Review.Conformance
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Shorter minimality proof (review proposal, same statements)

The witness argument in `prime_dvd_period_of_mem_R` (two nested CRT
constructions plus `Rrest`) can be replaced by an orbit argument:

* one good point `n` exists (`exists_good_of_admissible`);
* a period `T` keeps `n + j*T` good for every `j`;
* if a prime `q ∣ N` does not divide `T`, `T` is invertible mod `q`, so some
  `j` makes `q ∣ n + j*T`, contradicting coprimality with `N`.

This proves `q ∣ T` for *every* prime `q ∣ N` (not only `q ∈ Rset`), hence
`rad N ∣ T`, and `Tmin = lcm(m, rad N) ∣ T` follows from `Nat.lcm_dvd`.
`Rset`/`Rrest`/`coprime_q_Rrest`/`R_eq_q_mul_Rrest` are then no longer needed.
-/

namespace GDTReadingPoint

theorem IsPeriod.good_add_mul
    {P : Params} {T : ℕ} (hT : IsPeriod P T) {n : ℕ} (hn : Good P n) :
    ∀ j, Good P (n + j * T) := by
  intro j
  induction j with
  | zero => simpa using hn
  | succ j ih =>
    have := (hT (n + j * T)).2 ih
    rwa [Nat.add_assoc, ← Nat.succ_mul] at this

theorem prime_dvd_period
    (P : Params) (hadm : Admissible P.a (Params.d P))
    {T q : ℕ} (hT : IsPeriod P T) (hq : q ∈ P.N.primeFactors) :
    q ∣ T := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨n, hn⟩ := exists_good_of_admissible P hadm
  by_contra hqT
  have hunit : IsUnit (T : ZMod q) :=
    (ZMod.isUnit_iff_coprime T q).2
      (Nat.coprime_comm.mp ((hqp.coprime_iff_not_dvd).2 hqT))
  let j : ℕ := (-(n : ZMod q) * (T : ZMod q)⁻¹).val
  have hdiv : q ∣ n + j * T := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    haveI : NeZero q := ⟨hqp.ne_zero⟩
    rw [ZMod.natCast_zmod_val, mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one,
      add_neg_cancel]
  have hcop : Nat.Coprime q P.N :=
    Nat.Coprime.coprime_dvd_left hdiv (hT.good_add_mul hn j).2
  exact (hqp.coprime_iff_not_dvd.mp hcop) (Nat.dvd_of_mem_primeFactors hq)

theorem radN_dvd_period
    (P : Params) (hadm : Admissible P.a (Params.d P))
    {T : ℕ} (hT : IsPeriod P T) :
    Params.radN P ∣ T :=
  Finset.prod_primes_dvd T
    (fun _ hq => (Nat.prime_of_mem_primeFactors hq).prime)
    (fun _ hq => prime_dvd_period P hadm hT hq)

/-- Same statement as `Tmin_dvd_period`, via `Tmin = lcm(m, rad N)`. -/
theorem Tmin_dvd_period'
    (P : Params) (hadm : Admissible P.a (Params.d P))
    {T : ℕ} (hT : IsPeriod P T) :
    Params.Tmin P ∣ T := by
  rw [Params.Tmin_eq_lcm]
  exact Nat.lcm_dvd (m_dvd_period P hadm hT) (radN_dvd_period P hadm hT)

end GDTReadingPoint
