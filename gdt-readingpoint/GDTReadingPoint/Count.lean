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

  have hleft :
      (Window P (k + 1)).filter (Good P) =
        (((Window P k).filter (Good P)).erase k).insert (k + T) := by
    ext n
    simp [Window, T, good_shift_Tmin_iff]
    omega

  rw [hleft]

  by_cases hk : Good P k

  · have hk_mem :
        k ∈ (Window P k).filter (Good P) := by
      simp [Window, hk, T]
      have hTpos : 0 < T := by
        unfold T Params.Tmin
        exact Nat.mul_pos P.hm (by
          unfold Params.R
          apply Finset.prod_pos
          intro q hq
          exact (Nat.prime_of_mem_primeFactors
            (Finset.mem_sdiff.mp hq).1).pos)
      omega

    have hkT_not_mem :
        k + T ∉ ((Window P k).filter (Good P)).erase k := by
      intro h
      have hmem :
          k + T ∈ (Window P k).filter (Good P) :=
        Finset.mem_of_mem_erase h
      have hbounds :=
        (mem_Window_iff P k (k + T)).1
          (Finset.mem_filter.mp hmem).1
      omega

    rw [Finset.card_insert_of_not_mem hkT_not_mem]
    rw [Finset.card_erase_of_mem hk_mem]

  · have hk_not_mem :
        k ∉ (Window P k).filter (Good P) := by
      simp [hk]

    have hkT_not_good : ¬ Good P (k + T) := by
      intro h
      exact hk ((good_shift_Tmin_iff P k).1 h)

    have hkT_not_mem :
        k + T ∉ ((Window P k).filter (Good P)).erase k := by
      intro h
      have hmem :
          k + T ∈ (Window P k).filter (Good P) :=
        Finset.mem_of_mem_erase h
      exact hkT_not_good (Finset.mem_filter.mp hmem).2

    rw [Finset.card_insert_of_not_mem hkT_not_mem]
    rw [Finset.erase_eq_of_not_mem hk_not_mem]

    have hkT_not_in_insert :
        k + T ∉ (Window P k).filter (Good P) := by
      intro h
      exact hkT_not_good (Finset.mem_filter.mp h).2

    rw [Finset.card_insert_of_not_mem hkT_not_in_insert]

end GDTReadingPoint
