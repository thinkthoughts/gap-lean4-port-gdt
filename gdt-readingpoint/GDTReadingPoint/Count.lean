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

end GDTReadingPoint
