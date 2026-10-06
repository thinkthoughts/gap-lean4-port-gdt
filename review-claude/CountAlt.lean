import Review.Conformance

/-!
# Shorter per-period count (review proposal, same statement)

PDF step: "gcd(n,N)=1 ⟺ gcd(n,R)=1 on the admissible class", then CRT
bijection `n ↦ n mod R` between the class inside `[0, mR)` and `ℤ/Rℤ`.

`good_iff_coprime_R` packages the first step once (it is currently re-derived
inline in `Nonempty`, `Minimal`, and `Count`). The count then uses an explicit
inverse (`Finset.card_nbij'` with `Nat.chineseRemainder`) instead of the
`residuePoint` / `residueImage` parametrization.
-/

namespace GDTReadingPoint

/-- PDF: on an admissible class, coprimality to `N` reduces to coprimality to `R`. -/
theorem good_iff_coprime_R
    (P : Params) (hadm : Admissible P.a (Params.d P)) (n : ℕ) :
    Good P n ↔ Nat.ModEq P.m n P.a ∧ Nat.Coprime n (Params.R P) := by
  constructor
  · rintro ⟨hres, hcop⟩
    exact ⟨hres, ((Params.coprime_radN_iff P n).2 hcop).of_dvd_right
      (Params.R_dvd_radN P)⟩
  · rintro ⟨hres, hcopR⟩
    refine ⟨hres, (Params.coprime_radN_iff P n).1 ?_⟩
    rw [← Params.d_mul_R P]
    refine Nat.Coprime.mul_right ?_ hcopR
    rw [Nat.coprime_iff_gcd_eq_one, (hres.of_dvd (Params.d_dvd_m P)).gcd_eq]
    exact hadm.gcd_eq_one

theorem count_Tmin_eq_totient_R
    (P : Params) (hadm : Admissible P.a (Params.d P)) :
    Nat.count (Good P) (Params.Tmin P) = Nat.totient (Params.R P) := by
  have hR := Params.R_pos P
  have co := Params.coprime_m_R P
  let crt : ℕ → ℕ := fun r => (Nat.chineseRemainder co P.a r).1
  rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
  apply Finset.card_nbij' (fun n => n % Params.R P) crt
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn ⊢
    refine ⟨Nat.mod_lt _ hR, ?_⟩
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one,
      (Nat.mod_modEq n (Params.R P)).gcd_eq, ← Nat.coprime_iff_gcd_eq_one]
    exact ((good_iff_coprime_R P hadm n).1 hn.2).2
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr ⊢
    refine ⟨Nat.chineseRemainder_lt_mul co _ _ P.hm.ne' hR.ne', ?_⟩
    refine (good_iff_coprime_R P hadm _).2 ⟨(Nat.chineseRemainder co P.a r).2.1, ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one, (Nat.chineseRemainder co P.a r).2.2.gcd_eq,
      Nat.gcd_comm]
    exact hr.2
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
    have hgood := (good_iff_coprime_R P hadm n).1 hn.2
    have h := Nat.chineseRemainder_modEq_unique co hgood.1
      (Nat.mod_modEq n (Params.R P)).symm
    show crt (n % Params.R P) = n
    exact h.symm.eq_of_lt_of_lt
      (Nat.chineseRemainder_lt_mul co _ _ P.hm.ne' hR.ne') hn.1
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr
    have h : crt r % Params.R P = r % Params.R P := (Nat.chineseRemainder co P.a r).2.2
    show crt r % Params.R P = r
    rw [h, Nat.mod_eq_of_lt hr.1]

/-- Same statement as `goodCount_eq_totient_R`. -/
theorem goodCount_eq_totient_R'
    (P : Params) (hadm : Admissible P.a (Params.d P)) (k : ℕ) :
    goodCount P k = Nat.totient (Params.R P) := by
  rw [goodCount_eq_count, count_Tmin_eq_totient_R P hadm]

end GDTReadingPoint
