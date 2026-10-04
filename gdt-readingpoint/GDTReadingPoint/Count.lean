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
        ∃ x ∈ (Window P k).filter (Good P),
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

end GDTReadingPoint
