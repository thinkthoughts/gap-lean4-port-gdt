import Mathlib.Data.Nat.ModEq
import GDTReadingPoint.Admissible
import GDTReadingPoint.Good

namespace GDTReadingPoint

/--
If the GDT residue is non-admissible at `d`, the conditioned set is empty.

This is the non-admissible branch of the GDT dichotomy.
-/
theorem empty_of_not_admissible
    (P : Params)
    (hbad : ¬ Admissible P.a (Params.d P)) :
    ∀ n, ¬ Good P n := by
  intro n hn
  apply hbad

  have hmod_m : Nat.ModEq P.m n P.a := hn.1

  have hmod_d : Nat.ModEq (Params.d P) n P.a :=
    hmod_m.of_dvd (Params.d_dvd_m P)

  have hn_coprime_d : Nat.Coprime n (Params.d P) :=
    hn.2.of_dvd_right (Params.d_dvd_N P)

  unfold Admissible
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← hmod_d.gcd_eq]
  exact hn_coprime_d.gcd_eq_one

end GDTReadingPoint
