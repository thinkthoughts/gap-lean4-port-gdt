import GDTReadingPoint.Nonempty
import GDTReadingPoint.Period

namespace GDTReadingPoint

/--
`T` is a period of the GDT-conditioned set if translation by `T`
preserves membership for every natural reading point.
-/
def IsPeriod (P : Params) (T : Nat) : Prop :=
  ∀ n, Good P (n + T) ↔ Good P n

/--
The specified GDT period `Tmin = mR` is a period of the conditioned set.
-/
theorem Tmin_isPeriod (P : Params) :
    IsPeriod P (Params.Tmin P) := by
  intro n
  exact good_add_Tmin_iff P n

/--
For an admissible GDT class, every period is divisible by `m`.
-/
theorem m_dvd_period
    (P : Params)
    (hadm : Admissible P.a (Params.d P))
    {T : Nat}
    (hT : IsPeriod P T) :
    P.m ∣ T := by
  rcases exists_good_of_admissible P hadm with ⟨n, hn⟩

  have hnT : Good P (n + T) :=
    (hT n).2 hn

  rcases hn with ⟨hnres, hncop⟩
  rcases hnT with ⟨hnTres, hnTcop⟩

  change Nat.ModEq P.m n P.a at hnres
  change Nat.ModEq P.m (n + T) P.a at hnTres

  have hmod : Nat.ModEq P.m (n + T) n :=
    hnTres.trans hnres.symm

  exact Nat.add_modEq_left_iff.mp hmod

/--
Every prime in the complementary radical support `Rset`
divides every period of an admissible GDT class.

The proof constructs a CRT witness engineered so that translation
by `T` introduces divisibility by `q`, contradicting preservation
of the coprimality condition unless `q ∣ T`.
-/
theorem prime_dvd_period_of_mem_R
    (P : Params)
    (hadm : Admissible P.a (Params.d P))
    {T q : Nat}
    (hT : IsPeriod P T)
    (hq : q ∈ Params.Rset P) :
    q ∣ T := by

  have hqprime : Nat.Prime q := by
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hq).1

  have hqR : q ∣ Params.R P := by
    rw [Params.R_eq_q_mul_Rrest P hq]
    exact dvd_mul_right q (Params.Rrest P q)

  by_contra hqT

  have hTmod_ne : T % q ≠ 0 := by
    intro hzero
    apply hqT
    exact Nat.dvd_of_mod_eq_zero hzero

  /-
  First CRT stage:

      b ≡ -T  (mod q)
      b ≡ 1   (mod Rrest)

  `q - T % q` represents `-T mod q`.
  -/
  let b :=
    Nat.chineseRemainder
      (Params.coprime_q_Rrest P hq)
      (q - T % q)
      1

  /-
  Second CRT stage:

      n ≡ a  (mod m)
      n ≡ b  (mod R)
  -/
  let n :=
    Nat.chineseRemainder
      (Params.coprime_m_R P)
      P.a
      b.1

  have hn_m :
      Nat.ModEq P.m n.1 P.a :=
    n.2.1

  have hn_R :
      Nat.ModEq (Params.R P) n.1 b.1 :=
    n.2.2

  have hb_q :
      Nat.ModEq q b.1 (q - T % q) :=
    b.2.1

  have hb_Rrest :
      Nat.ModEq (Params.Rrest P q) b.1 1 :=
    b.2.2

  have hn_q :
      Nat.ModEq q n.1 (q - T % q) := by
    have hn_b_q :
        Nat.ModEq q n.1 b.1 :=
      hn_R.of_dvd hqR
    exact hn_b_q.trans hb_q

  sorry

end GDTReadingPoint
