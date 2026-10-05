import Mathlib.Data.Finset.Interval
import GDTReadingPoint.Minimal
import Mathlib.Tactic

namespace GDTReadingPoint

/--
`Good P n` is decidable because both the residue condition
and natural-number coprimality are decidable.
-/
instance goodDecidable
    (P : Params)
    (n : Nat) :
    Decidable (Good P n) := by
  unfold Good
  infer_instance

/--
The half-open GDT counting window

    [k, k + Tmin)

at an arbitrary reading point `k`.
-/
def Window (P : Params) (k : Nat) : Finset Nat :=
  Finset.Ico k (k + Params.Tmin P)

/--
The number of GDT-good natural numbers in the half-open window

    [k, k + Tmin).
-/
def goodCount (P : Params) (k : Nat) : Nat :=
  ((Window P k).filter (Good P)).card

/--
Membership in the counting window is exactly the expected
half-open interval condition.
-/
theorem mem_Window_iff
    (P : Params)
    (k n : Nat) :
    n ∈ Window P k ↔
      k ≤ n ∧ n < k + Params.Tmin P := by
  simp [Window]

/--
Every GDT counting window has exactly `Tmin` natural reading points.
-/
theorem card_Window
    (P : Params)
    (k : Nat) :
    (Window P k).card = Params.Tmin P := by
  simp [Window]

/--
A natural number contributes to `goodCount` exactly where it lies
in the specified window and satisfies the GDT condition.
-/
theorem mem_good_filter_iff
    (P : Params)
    (k n : Nat) :
    n ∈ (Window P k).filter (Good P) ↔
      k ≤ n ∧
      n < k + Params.Tmin P ∧
      Good P n := by
  simp [Window, and_assoc]

/--
GDT membership repeats after one full `Tmin` interval.
-/
theorem good_shift_Tmin_iff
    (P : Params)
    (n : Nat) :
    Good P (n + Params.Tmin P) ↔ Good P n := by
  exact good_add_Tmin_iff P n

/--
Shifting the start of a counting window by one full period
preserves the number of GDT-good reading points.
-/
theorem goodCount_add_Tmin
    (P : Params)
    (k : Nat) :
    goodCount P (k + Params.Tmin P) =
      goodCount P k := by
  unfold goodCount

  let T := Params.Tmin P

  have hforward :
      ∀ n ∈ (Window P k).filter (Good P),
        n + T ∈
          (Window P (k + T)).filter (Good P) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    rcases hn with ⟨hnWindow, hnGood⟩
    constructor
    · rw [mem_Window_iff] at hnWindow ⊢
      omega
    · exact (good_shift_Tmin_iff P n).2 hnGood

  have hinjective :
      ∀ a ∈ (Window P k).filter (Good P),
        ∀ b ∈ (Window P k).filter (Good P),
          a + T = b + T → a = b := by
    intro a ha b hb hab
    omega

  have hsurjective :
      ∀ y ∈ (Window P (k + T)).filter (Good P),
        ∃ x,
          ∃ hx : x ∈ (Window P k).filter (Good P),
            x + T = y := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rcases hy with ⟨hyWindow, hyGood⟩

    have hyBounds :
        k + T ≤ y ∧
        y < k + T + Params.Tmin P := by
      exact (mem_Window_iff P (k + T) y).1 hyWindow

    refine ⟨y - T, ?_, ?_⟩

    · rw [Finset.mem_filter]
      constructor
      · apply (mem_Window_iff P k (y - T)).2
        dsimp [T] at hyBounds ⊢
        omega
      · have hyEq : y - T + T = y := by
          omega

        have hshift :
            Good P ((y - T) + Params.Tmin P) := by
          simpa [T, hyEq] using hyGood

        exact
          (good_shift_Tmin_iff P (y - T)).1 hshift

    · omega

  have hcard :
      ((Window P k).filter (Good P)).card =
        ((Window P (k + T)).filter (Good P)).card := by
    apply Finset.card_bij (fun n _ => n + T)
    · exact hforward
    · exact hinjective
    · exact hsurjective

  simpa [T] using hcard.symm

/--
Shifting the start of a counting window by any multiple of `Tmin`
preserves the number of GDT-good reading points.
-/
theorem goodCount_add_mul_Tmin
    (P : Params)
    (k r : Nat) :
    goodCount P (k + r * Params.Tmin P) =
      goodCount P k := by
  induction r with
  | zero =>
      simp

  | succ r ihr =>
      calc
        goodCount P (k + (r + 1) * Params.Tmin P)
            =
          goodCount P ((k + r * Params.Tmin P) + Params.Tmin P) := by
            simp [Nat.add_mul, Nat.add_assoc]
        _ = goodCount P (k + r * Params.Tmin P) := by
              exact goodCount_add_Tmin P (k + r * Params.Tmin P)
        _ = goodCount P k := ihr

/--
Shifting a length-`Tmin` counting window forward by one reading point
preserves the number of GDT-good values.
-/
theorem goodCount_succ
    (P : Params)
    (k : Nat) :
    goodCount P (k + 1) = goodCount P k := by
  unfold goodCount

  let T := Params.Tmin P

  have hRpos : 0 < Params.R P := by
    unfold Params.R
    apply Finset.prod_pos
    intro q hq
    exact
      (Nat.prime_of_mem_primeFactors
        (Finset.mem_sdiff.mp hq).1).pos

  have hTpos : 0 < T := by
    simp only [T]
    exact Nat.mul_pos P.hm hRpos

  /-
  Cyclic shift of one period:

      k       ↦ k + T
      n ≠ k   ↦ n
  -/
  let f : Nat → Nat :=
    fun n => if n = k then k + T else n

  have hforward :
      ∀ n ∈ (Window P k).filter (Good P),
        f n ∈ (Window P (k + 1)).filter (Good P) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    rcases hn with ⟨hnWindow, hnGood⟩

    have hnBounds :
        k ≤ n ∧ n < k + Params.Tmin P :=
      (mem_Window_iff P k n).1 hnWindow

    by_cases hnk : n = k

    · subst n
      constructor
      · apply (mem_Window_iff P (k + 1) (f k)).2
        dsimp [f]
        simp
        simp only [T] at hTpos ⊢
        omega
      · dsimp [f]
        simp
        simp only [T]
        exact (good_shift_Tmin_iff P k).2 hnGood

    · constructor
      · apply (mem_Window_iff P (k + 1) (f n)).2
        dsimp [f]
        simp [hnk]
        omega
      · dsimp [f]
        simp [hnk, hnGood]

  have hinjective :
      ∀ a ∈ (Window P k).filter (Good P),
        ∀ b ∈ (Window P k).filter (Good P),
          f a = f b → a = b := by
    intro a ha b hb hab

    have haWindow :=
      (Finset.mem_filter.mp ha).1

    have hbWindow :=
      (Finset.mem_filter.mp hb).1

    have haBounds :
        k ≤ a ∧ a < k + Params.Tmin P :=
      (mem_Window_iff P k a).1 haWindow

    have hbBounds :
        k ≤ b ∧ b < k + Params.Tmin P :=
      (mem_Window_iff P k b).1 hbWindow

    by_cases hak : a = k

    · subst a
      by_cases hbk : b = k
      · exact hbk.symm
      · dsimp [f] at hab
        simp [hbk] at hab
        simp only [T] at haBounds hbBounds hab
        omega

    · by_cases hbk : b = k

      · subst b
        dsimp [f] at hab
        simp [hak] at hab
        simp only [T] at haBounds hbBounds hab
        omega

      · dsimp [f] at hab
        simp [hak, hbk] at hab
        exact hab

  have hsurjective :
      ∀ y ∈ (Window P (k + 1)).filter (Good P),
        ∃ x,
          ∃ hx : x ∈ (Window P k).filter (Good P),
            f x = y := by
    intro y hy

    rw [Finset.mem_filter] at hy
    rcases hy with ⟨hyWindow, hyGood⟩

    have hyBounds :
        k + 1 ≤ y ∧
        y < k + 1 + Params.Tmin P :=
      (mem_Window_iff P (k + 1) y).1 hyWindow

    by_cases hyEnd : y = k + T

    · refine ⟨k, ?_, ?_⟩

      · rw [Finset.mem_filter]
        constructor
        · apply (mem_Window_iff P k k).2
          simp only [T] at hTpos ⊢
          omega
        · have hyGood' : Good P (k + Params.Tmin P) := by
            simpa [T, hyEnd] using hyGood
          exact (good_shift_Tmin_iff P k).1 hyGood'

      · dsimp [f]
        simp [hyEnd]

    · refine ⟨y, ?_, ?_⟩

      · rw [Finset.mem_filter]
        constructor
        · apply (mem_Window_iff P k y).2
          simp only [T] at hyEnd ⊢
          omega
        · exact hyGood

      · dsimp [f]
        have hy_ne_k : y ≠ k := by
          omega
        simp [hy_ne_k]

  have hcard :
      ((Window P k).filter (Good P)).card =
        ((Window P (k + 1)).filter (Good P)).card := by
    apply Finset.card_bij (fun n _ => f n)
    · exact hforward
    · exact hinjective
    · exact hsurjective

  exact hcard.symm

/--
Every length-`Tmin` counting window has the same number of
GDT-good reading points as the initial window.
-/
theorem goodCount_eq_zero
    (P : Params)
    (k : Nat) :
    goodCount P k = goodCount P 0 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        goodCount P (k + 1) = goodCount P k :=
          goodCount_succ P k
        _ = goodCount P 0 := ih

/--
The unique point in the residue class `a mod m`
corresponding to parameter `t`.
-/
def residuePoint
    (P : Params)
    (t : Nat) : Nat :=
  P.a % P.m + P.m * t

/--
For `t < R`, the corresponding residue-class point lies
inside the initial period `[0, Tmin)`.
-/
theorem residuePoint_lt_Tmin
    (P : Params)
    {t : Nat}
    (ht : t < Params.R P) :
    residuePoint P t < Params.Tmin P := by
  unfold residuePoint Params.Tmin

  have ha_lt :
      P.a % P.m < P.m :=
    Nat.mod_lt P.a P.hm

  have ht1 :
      t + 1 ≤ Params.R P :=
    Nat.succ_le_of_lt ht

  calc
    P.a % P.m + P.m * t
        < P.m + P.m * t := by
            exact Nat.add_lt_add_right ha_lt (P.m * t)

    _ = P.m * (t + 1) := by
          rw [Nat.mul_succ]
          ac_rfl

    _ ≤ P.m * Params.R P := by
          exact Nat.mul_le_mul_left P.m ht1

/--
`residuePoint P t` always lies in the residue class `a mod m`.
-/
theorem residuePoint_mod_m
    (P : Params)
    (t : Nat) :
    residuePoint P t % P.m = P.a % P.m := by
  unfold residuePoint
  rw [Nat.add_mod, Nat.mul_mod]
  simp

/--
The affine parametrization `t ↦ a mod m + m*t` is injective.
-/
theorem residuePoint_injective
    (P : Params) :
    Function.Injective (residuePoint P) := by
  intro t₁ t₂ h

  unfold residuePoint at h

  have hmpos : 0 < P.m := P.hm

  have hmul :
      P.m * t₁ = P.m * t₂ := by
    exact Nat.add_left_cancel h

  exact Nat.eq_of_mul_eq_mul_left hmpos hmul

/--
Every natural number in the specified residue class has the affine
form `a mod m + m*t`.
-/
theorem exists_residuePoint_of_mod_eq
    (P : Params)
    {n : Nat}
    (hmod : n % P.m = P.a % P.m) :
    ∃ t, n = residuePoint P t := by
  refine ⟨n / P.m, ?_⟩

  unfold residuePoint

  have hdecomp :
      n = n % P.m + P.m * (n / P.m) := by
    rw [Nat.mod_add_div]

  rw [hmod] at hdecomp

  exact hdecomp

/--
If a residue-class point lies in the initial period `[0, Tmin)`,
then its affine parameter satisfies `t < R`.
-/
theorem residuePoint_index_lt_R
    (P : Params)
    {n t : Nat}
    (hnlt : n < Params.Tmin P)
    (hn : n = residuePoint P t) :
    t < Params.R P := by
  subst n
  unfold residuePoint Params.Tmin at hnlt

  by_contra hnot

  have hRle :
      Params.R P ≤ t :=
    Nat.le_of_not_gt hnot

  have hmul :
      P.m * Params.R P ≤ P.m * t :=
    Nat.mul_le_mul_left P.m hRle

  have hbase :
      P.m * t ≤ P.a % P.m + P.m * t :=
    Nat.le_add_left _ _

  exact
    (Nat.not_lt_of_ge (le_trans hmul hbase)) hnlt

/--
Every point in the initial period `[0, Tmin)` satisfying the
specified residue condition is represented by a parameter `t < R`.
-/
theorem exists_residuePoint_lt_R
    (P : Params)
    {n : Nat}
    (hnlt : n < Params.Tmin P)
    (hmod : n % P.m = P.a % P.m) :
    ∃ t < Params.R P, n = residuePoint P t := by
  rcases exists_residuePoint_of_mod_eq P hmod with ⟨t, ht⟩

  refine ⟨t, ?_, ht⟩

  exact residuePoint_index_lt_R P hnlt ht
/--
For an admissible residue class, a parametrized residue point is
GDT-good exactly where it is coprime to the complementary factor `R`.
-/
theorem good_residuePoint_iff_coprime_R
    (P : Params)
    (hadm : Admissible P.a (Params.d P))
    (t : Nat) :
    Good P (residuePoint P t) ↔
      Nat.Coprime (residuePoint P t) (Params.R P) := by
  constructor

  · intro hgood

    have hcop_radN :
        Nat.Coprime (residuePoint P t) (Params.radN P) :=
      (Params.coprime_radN_iff P (residuePoint P t)).2 hgood.2

    have hR_dvd_radN :
        Params.R P ∣ Params.radN P := by
      refine ⟨Params.d P, ?_⟩
      rw [← Params.d_mul_R P]
      ac_rfl

    exact hcop_radN.of_dvd_right hR_dvd_radN

  · intro hcop_R

    have hmod_m :
        Nat.ModEq P.m (residuePoint P t) P.a := by
      change
        residuePoint P t % P.m = P.a % P.m
      exact residuePoint_mod_m P t

    have hmod_d :
        Nat.ModEq (Params.d P) (residuePoint P t) P.a :=
      hmod_m.of_dvd (Params.d_dvd_m P)

    have hcop_d :
        Nat.Coprime (residuePoint P t) (Params.d P) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      rw [hmod_d.gcd_eq]
      exact hadm.gcd_eq_one

    have hcop_radN :
        Nat.Coprime (residuePoint P t) (Params.radN P) := by
      rw [← Params.d_mul_R P]
      exact hcop_d.mul_right hcop_R

    have hcop_N :
        Nat.Coprime (residuePoint P t) P.N :=
      (Params.coprime_radN_iff P (residuePoint P t)).1
        hcop_radN

    constructor
    · exact residuePoint_mod_m P t
    · exact hcop_N

/--
On the range `t < R`, reduction of `residuePoint P t` modulo `R`
is injective.
-/
theorem residuePoint_mod_R_injective
    (P : Params)
    {t₁ t₂ : Nat}
    (ht₁ : t₁ < Params.R P)
    (ht₂ : t₂ < Params.R P)
    (h :
      residuePoint P t₁ % Params.R P =
      residuePoint P t₂ % Params.R P) :
    t₁ = t₂ := by

  have hmod :
      Nat.ModEq (Params.R P)
        (residuePoint P t₁)
        (residuePoint P t₂) := by
    exact h

  unfold residuePoint at hmod

  have hmul :
      Nat.ModEq (Params.R P)
        (P.m * t₁)
        (P.m * t₂) := by
    exact
      Nat.ModEq.add_left_cancel'
        (P.a % P.m)
        hmod

  have hcop :
      Nat.gcd (Params.R P) P.m = 1 := by
    exact (Params.coprime_m_R P).symm.gcd_eq_one

  have htmod :
      Nat.ModEq (Params.R P) t₁ t₂ :=
    Nat.ModEq.cancel_left_of_coprime hcop hmul

  exact htmod.eq_of_lt_of_lt ht₁ ht₂

/--
The residues modulo `R` reached by the affine parametrization
`t ↦ residuePoint P t`, with `t` ranging over `0, ..., R-1`.
-/
def residueImage (P : Params) : Finset Nat :=
  (Finset.range (Params.R P)).image
    (fun t => residuePoint P t % Params.R P)

/--
The affine residue map hits `R` distinct residues.
-/
theorem card_residueImage
    (P : Params) :
    (residueImage P).card = Params.R P := by
  unfold residueImage

  have hinj :
      Set.InjOn
        (fun t => residuePoint P t % Params.R P)
        (↑(Finset.range (Params.R P)) : Set Nat) := by
    intro t₁ ht₁ t₂ ht₂ h
    have ht₁' : t₁ < Params.R P := by
      exact Finset.mem_range.mp ht₁
    have ht₂' : t₂ < Params.R P := by
      exact Finset.mem_range.mp ht₂
    exact residuePoint_mod_R_injective P ht₁' ht₂' h

  calc
    ((Finset.range (Params.R P)).image
        (fun t => residuePoint P t % Params.R P)).card
        =
      (Finset.range (Params.R P)).card := by
        exact Finset.card_image_of_injOn hinj
    _ = Params.R P := by
          simp

/--
The affine residue map permutes the complete residue system modulo `R`.
-/
theorem residueImage_eq_range
    (P : Params) :
    residueImage P = Finset.range (Params.R P) := by
  apply Finset.eq_of_subset_of_card_le

  · intro x hx
    rw [residueImage, Finset.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩

    have hRpos : 0 < Params.R P := by
      unfold Params.R
      apply Finset.prod_pos
      intro q hq
      exact
        (Nat.prime_of_mem_primeFactors
          (Finset.mem_sdiff.mp hq).1).pos

    exact Finset.mem_range.mpr
      (Nat.mod_lt (residuePoint P t) hRpos)

  · rw [card_residueImage]
    simp

end GDTReadingPoint
