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

  let b :=
    Nat.chineseRemainder
      (Params.coprime_q_Rrest P hq)
      (q - T % q)
      1

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

  have hq_dvd_nT : q ∣ n.1 + T := by
    apply Nat.dvd_of_mod_eq_zero

    change (n.1 + T) % q = 0
    rw [Nat.add_mod]

    change n.1 % q = (q - T % q) % q at hn_q
    rw [hn_q]

    have hrpos : 0 < T % q :=
      Nat.pos_of_ne_zero hTmod_ne

    have hrlt : T % q < q :=
      Nat.mod_lt T hqprime.pos

    have hdiff_lt : q - T % q < q :=
      Nat.sub_lt hqprime.pos hrpos

    rw [Nat.mod_eq_of_lt hdiff_lt]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hrlt)]
    simp

  have hRrestR :
      Params.Rrest P q ∣ Params.R P := by
    rw [Params.R_eq_q_mul_Rrest P hq]
    exact ⟨q, by ac_rfl⟩

  have hn_Rrest :
      Nat.ModEq (Params.Rrest P q) n.1 1 := by
    have hn_b_Rrest :
        Nat.ModEq (Params.Rrest P q) n.1 b.1 :=
      hn_R.of_dvd hRrestR
    exact hn_b_Rrest.trans hb_Rrest

  have hcop_n_Rrest :
      Nat.Coprime n.1 (Params.Rrest P q) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [hn_Rrest.gcd_eq]
    simp

  have hq_not_dvd_n : ¬ q ∣ n.1 := by
    intro hdiv

    have hnmod0 : n.1 % q = 0 :=
      Nat.mod_eq_zero_of_dvd hdiv

    have hcong :
        n.1 % q = (q - T % q) % q := by
      exact hn_q

    have hrpos : 0 < T % q :=
      Nat.pos_of_ne_zero hTmod_ne

    have hrlt : T % q < q :=
      Nat.mod_lt T hqprime.pos

    have hdiff_pos : 0 < q - T % q :=
      Nat.sub_pos_of_lt hrlt

    have hdiff_lt : q - T % q < q :=
      Nat.sub_lt hqprime.pos hrpos

    have hdiffmod :
        (q - T % q) % q = q - T % q :=
      Nat.mod_eq_of_lt hdiff_lt

    rw [hnmod0, hdiffmod] at hcong

    exact (Nat.ne_of_gt hdiff_pos) hcong.symm

  have hcop_q_n :
      Nat.Coprime q n.1 :=
    (hqprime.coprime_iff_not_dvd).2 hq_not_dvd_n

  have hcop_n_q :
      Nat.Coprime n.1 q :=
    hcop_q_n.symm

  have hcop_n_R :
      Nat.Coprime n.1 (Params.R P) := by
    have hcop_prod :
        Nat.Coprime n.1 (q * Params.Rrest P q) :=
      hcop_n_q.mul_right hcop_n_Rrest

    have hR_dvd_prod :
        Params.R P ∣ q * Params.Rrest P q := by
      refine ⟨1, ?_⟩
      simpa using (Params.R_eq_q_mul_Rrest P hq).symm

    exact hcop_prod.of_dvd_right hR_dvd_prod

  have hn_d :
      Nat.ModEq (Params.d P) n.1 P.a :=
    hn_m.of_dvd (Params.d_dvd_m P)

  have hcop_n_d :
      Nat.Coprime n.1 (Params.d P) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [hn_d.gcd_eq]
    exact hadm.gcd_eq_one

  have hcop_n_radN :
      Nat.Coprime n.1 (Params.radN P) := by
    rw [← Params.d_mul_R P]
    exact hcop_n_d.mul_right hcop_n_R

  have hcop_n_N :
      Nat.Coprime n.1 P.N :=
    (Params.coprime_radN_iff P n.1).1 hcop_n_radN

  have hn_good : Good P n.1 := by
    constructor
    · exact hn_m
    · exact hcop_n_N

  have hnT_good : Good P (n.1 + T) :=
    (hT n.1).2 hn_good

  have hqNmem :
      q ∈ Nat.primeFactors P.N :=
    (Finset.mem_sdiff.mp hq).1

  have hq_dvd_N : q ∣ P.N :=
    (Nat.mem_primeFactors.mp hqNmem).2.1

  have hcop_q_N :
      Nat.Coprime q P.N :=
    hnT_good.2.of_dvd_left hq_dvd_nT

  exact
    (hqprime.coprime_iff_not_dvd.mp hcop_q_N)
      hq_dvd_N

end GDTReadingPoint
