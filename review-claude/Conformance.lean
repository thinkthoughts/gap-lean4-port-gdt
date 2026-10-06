import GDTReadingPoint.Density
import GDTReadingPoint.Empty
import Mathlib.Data.Nat.Periodic
import Mathlib.RingTheory.Radical

/-!
# Spec-conformance identities (review proposals)

Each statement ties a repo definition to the literal form used in `gdt.pdf`.
-/

namespace GDTReadingPoint
namespace Params

theorem R_pos (P : Params) : 0 < R P :=
  Finset.prod_pos fun _ hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos

theorem d_pos (P : Params) : 0 < d P :=
  Finset.prod_pos fun _ hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1).pos

theorem radN_pos (P : Params) : 0 < radN P :=
  Finset.prod_pos fun _ hq => (Nat.prime_of_mem_primeFactors hq).pos

theorem Tmin_pos (P : Params) : 0 < Tmin P :=
  Nat.mul_pos P.hm (R_pos P)

/-- `radN` is Mathlib's `UniqueFactorizationMonoid.radical` of `N`. -/
theorem radN_eq_radical (P : Params) :
    radN P = UniqueFactorizationMonoid.radical P.N := by
  rw [UniqueFactorizationMonoid.radical,
    UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
  rfl

/-- PDF: `d = rad(gcd(m, N))`. -/
theorem d_eq_radical_gcd (P : Params) :
    d P = UniqueFactorizationMonoid.radical (Nat.gcd P.m P.N) := by
  rw [UniqueFactorizationMonoid.radical,
    UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors,
    Nat.primeFactors_gcd P.hm.ne' P.hN.ne', Finset.inter_comm]
  rfl

/-- PDF: `R = rad(N) / d`. -/
theorem R_eq_radN_div_d (P : Params) : R P = radN P / d P := by
  rw [← d_mul_R P, Nat.mul_div_cancel_left _ (d_pos P)]

theorem R_dvd_radN (P : Params) : R P ∣ radN P :=
  Dvd.intro_left _ (d_mul_R P)

/-- PDF: `Tmin = m R = lcm(m, rad N)`. -/
theorem Tmin_eq_lcm (P : Params) : Tmin P = Nat.lcm P.m (radN P) := by
  apply Nat.dvd_antisymm
  · exact (coprime_m_R P).mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left _ _)
      ((R_dvd_radN P).trans (Nat.dvd_lcm_right _ _))
  · exact Nat.lcm_dvd (dvd_mul_right _ _) (radN_dvd_Tmin P)

end Params

/-- PDF: `Tmin` is the exact minimal *positive* period (admissible branch). -/
theorem Tmin_isLeast
    (P : Params) (hadm : Admissible P.a (Params.d P)) :
    IsLeast {T | 0 < T ∧ IsPeriod P T} (Params.Tmin P) :=
  ⟨⟨Params.Tmin_pos P, Tmin_isPeriod P⟩,
    fun _ ⟨hT0, hT⟩ => Nat.le_of_dvd hT0 (Tmin_dvd_period P hadm hT)⟩

/-- `Good` as a Mathlib `Function.Periodic` predicate. -/
theorem good_periodic (P : Params) :
    Function.Periodic (Good P) (Params.Tmin P) :=
  fun n => propext (good_add_Tmin_iff P n)

/--
Window-invariance in one line from Mathlib's
`Nat.filter_Ico_card_eq_of_periodic`. This subsumes `goodCount_succ`,
`goodCount_add_Tmin`, `goodCount_add_mul_Tmin` and `goodCount_eq_zero`.
-/
theorem goodCount_eq_count (P : Params) (k : ℕ) :
    goodCount P k = Nat.count (Good P) (Params.Tmin P) :=
  Nat.filter_Ico_card_eq_of_periodic k _ (Good P) (good_periodic P)

/-! ### The PDF counting function `S(L)` on `[1, L]` -/

/-- `|S(N, L, m, a)| = #{1 ≤ n ≤ L : n ≡ a (mod m), gcd(n, N) = 1}`. -/
def S (P : Params) (L : ℕ) : ℕ :=
  ((Finset.Icc 1 L).filter (Good P)).card

/-- Count over `q` consecutive full periods starting anywhere. -/
theorem card_filter_Ico_mul_Tmin
    (P : Params) (hadm : Admissible P.a (Params.d P)) (q : ℕ) :
    ∀ k, ((Finset.Ico k (k + q * Params.Tmin P)).filter (Good P)).card
      = q * Nat.totient (Params.R P) := by
  induction q with
  | zero => intro k; simp
  | succ q ih =>
    intro k
    have hsplit :
        Finset.Ico k (k + (q + 1) * Params.Tmin P) =
          Finset.Ico k (k + Params.Tmin P) ∪
            Finset.Ico (k + Params.Tmin P)
              ((k + Params.Tmin P) + q * Params.Tmin P) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih]
    have h1 : ((Finset.Ico k (k + Params.Tmin P)).filter (Good P)).card
        = Nat.totient (Params.R P) := goodCount_eq_totient_R P hadm k
    rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Shifting a window by a multiple of `Tmin` preserves the count. -/
theorem card_filter_Ico_add_mul_Tmin (P : Params) (q a b : ℕ) :
    ((Finset.Ico (a + q * Params.Tmin P) (b + q * Params.Tmin P)).filter
        (Good P)).card =
      ((Finset.Ico a b).filter (Good P)).card := by
  rw [← Finset.map_add_right_Ico, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Function.comp, addRightEmbedding_apply]
  exact iff_of_eq ((good_periodic P).nat_mul q n)

/-- PDF Theorem 3, count: `L = q·Tmin + s ⇒ |S(L)| = q φ(R) + R_rem(s)`. -/
theorem S_eq (P : Params) (hadm : Admissible P.a (Params.d P)) (q s : ℕ) :
    S P (q * Params.Tmin P + s) = q * Nat.totient (Params.R P) + S P s := by
  unfold S
  have hIcc : ∀ L, Finset.Icc 1 L = Finset.Ico 1 (L + 1) := fun L => by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, hIcc,
    show q * Params.Tmin P + s + 1 = (1 + q * Params.Tmin P) + s by omega,
    ← Finset.Ico_union_Ico_eq_Ico (b := 1 + q * Params.Tmin P) (by omega) (by omega),
    Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
    card_filter_Ico_mul_Tmin P hadm q 1]
  congr 1
  rw [show 1 + q * Params.Tmin P + s = (s + 1) + q * Params.Tmin P by omega,
    show 1 + q * Params.Tmin P = 1 + q * Params.Tmin P from rfl,
    card_filter_Ico_add_mul_Tmin]

/-- PDF: `|S(q·Tmin)| = q φ(R)`. -/
theorem S_mul_Tmin (P : Params) (hadm : Admissible P.a (Params.d P)) (q : ℕ) :
    S P (q * Params.Tmin P) = q * Nat.totient (Params.R P) := by
  have := S_eq P hadm q 0
  simpa [S] using this

/-- PDF: non-admissible branch, `S(L) = ∅` for every `L`. -/
theorem S_eq_zero_of_not_admissible
    (P : Params) (hbad : ¬ Admissible P.a (Params.d P)) (L : ℕ) :
    S P L = 0 := by
  unfold S
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  exact empty_of_not_admissible P hbad n

end GDTReadingPoint
