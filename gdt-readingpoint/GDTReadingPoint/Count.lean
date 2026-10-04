import Mathlib.Data.Finset.Interval
import GDTReadingPoint.Minimal

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

end GDTReadingPoint
