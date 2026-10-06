# GDT Reading Point: external review

**Scope:** `gdt-readingpoint/` against `gdt.pdf` (Draft v3.3) and the upstream GAP port, snapshot of 2026-10-05.
**Mode:** review, not rewrite. Every proposal below is a separate file in `gdt-review-proposals/`, kernel-checked against this snapshot (Lean v4.28.0, Mathlib v4.28.0): 0 `sorry`, 0 `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only.
**Build coverage:** I built every `GDTReadingPoint` module except `ZmodBridge`. Upstream `Zmodnz.lean` does `import Mathlib`, and the Mathlib binary cache was unreachable from my sandbox, so I checked bridge-level code against a body-identical copy of `Zmodnz.lean` with narrowed imports. `RequestProject` itself was outside the build.

---

## 0. Blocking finding: `Params` is uninhabited, so every theorem is vacuous

`Basic.lean` imports nothing. In that file the Mathlib notation `ℕ` is undefined, so Lean's `autoImplicit` treats `ℕ` as a fresh type variable for each field:

```text
GDTReadingPoint.Params.N : Params → {ℕ : Type} → ℕ
GDTReadingPoint.Params.a : Params → {ℕ : Sort u_1} → ℕ
```

A field of type `{α : Type} → α` must produce an element of *every* type, including `Empty`. So no `Params` exists, and the following compiles with **no axioms at all** (`VacuityDemo.lean`):

```lean
theorem params_empty (P : Params) : False := (@Params.N P Empty).elim

example (P : Params) (hadm : Admissible P.a (Params.d P)) (k : Nat) :
    goodCount P k = Nat.totient (Params.R P) + 1 := (params_empty P).elim
```

Downstream files import Mathlib, where `P.N` elaborates as `@Params.N P Nat`. That is why every statement reads correctly and every proof checks. The kernel accepted them because their hypothesis `P : Params` can never be met.

**The good news:** the mathematics survives intact. With the one-line fix, **all existing proofs compile unchanged.**

**Fix** (`0001-gdt-params-fix.patch`, 5 files, +22/−13):

1. `Basic.lean`: write the field types as `Nat`.
2. `lakefile.toml`: set `leanOptions = { autoImplicit = false }` on the `GDTReadingPoint` lib. I verified that the original mistake then becomes a hard error ("Unknown identifier `ℕ`").
3. `Examples.lean`: add the regression guard `example : Params := ⟨18, 2, 1, by decide, by decide⟩`.
4. CI: add `lake build GDTReadingPoint`. The current workflow builds only `RequestProject`, so the GDT library was never kernel-checked in CI.

**Second build break, in the same patch:** `Examples.lean` fails to compile on the pinned toolchain (`failed to synthesize Decidable (Admissible 1 30)`). `Admissible` is a plain `def`, which hides `Nat.Coprime`'s `Decidable` instance. The fix is `unfold Admissible; decide`, or make `Admissible` an `abbrev`. Because the root module imports `Examples`, `lake build GDTReadingPoint` fails on this snapshot.

**Lesson for the loop:** "builds with 0 `sorry`" is necessary and insufficient. Each new structure needs one concrete inhabitant, and that is exactly the role the PDF examples play (§6).

---

## 1. Specification coverage

| PDF claim | Lean realization (current) | Status | Proposal |
|---|---|---|---|
| Lemma 2.1, exponent-blindness `k/φ(k) = rad k/φ(rad k)` | missing | **gap** | `totient_mul_rad` (ℕ form, all `k`), `div_totient_eq_rad` (ratio, `k ≥ 1`) |
| `d = rad(gcd(m,N))` | `Params.d := ∏ (N.pf ∩ m.pf)` | definition matches; identity unstated | `d_eq_radical_gcd` (against Mathlib `radical`) |
| `rad N` | `Params.radN := ∏ N.pf` | matches | `radN_eq_radical` |
| `R = rad(N)/d` | `d_mul_R : d * R = radN` | multiplicative form proven | `R_eq_radN_div_d` |
| `gcd(m, R) = 1` | `coprime_m_R` | ✔ | — |
| Dichotomy, non-admissible ⇒ `S(L) = ∅` | `empty_of_not_admissible` (for all `n`) | ✔ stronger | `S_eq_zero_of_not_admissible` (literal form) |
| Admissible ⇒ accepted point exists | `exists_good_of_admissible` | ✔ (used inside the PDF's minimality proof) | — |
| `Tmin` is a period | `good_add_Tmin_iff`, `Tmin_isPeriod` | ✔ (unconditional, stronger) | — |
| Every period is a multiple of `Tmin` | `Tmin_dvd_period` | ✔ | shorter proof, §4 |
| `Tmin` is the **minimal positive** period | implied, unpackaged | small gap | `Tmin_isLeast : IsLeast {T \| 0 < T ∧ IsPeriod P T} Tmin` |
| `Tmin = mR = lcm(m, rad N)` | `Tmin := m * R` | **lcm form missing** | `Tmin_eq_lcm` |
| `φ(R)` accepted per **any** length-`Tmin` window | `goodCount_eq_totient_R` (any start `k`) | ✔ | shorter proof, §4 |
| `\|S(qTmin)\| = qφ(R)`; `\|S(L)\| = qφ(R) + R_rem(s)` | missing (no `S` on `[1, L]`) | **gap** | `S`, `S_mul_Tmin`, `S_eq` |
| density `φ(R)/(mR)` | `density`, `goodCount_div_Tmin_eq_density` | ✔ (definitional) | — |
| `C(N,m) = d/φ(d)` vs naive `φ(N)/(Nm)` | `correctionFactor` def + `totient_radN_eq_mul` | **headline gap** | `density_eq_correctionFactor_mul_naive`, `density_div_naive_eq_correctionFactor` |
| `C = ∏_{p∣gcd(m,N)} p/(p−1)` | missing | minor gap | follows from `Nat.totient_eq_mul_prod_factors` |
| Independence of admissible `a` | statements mention `a` only via `hadm` | ✔ structurally | — |
| `a ∈ ℤ` | `Params.a : ℕ` | representation gap | see §3 |
| §3.1–3.4 specializations (Thm 2, 1′, 1) | missing | gap | next phase, §6 |
| §3.3 examples (18,2,1) and (5,6,2) | missing (`Examples.lean` checks only `Coprime 1 30`) | **gap** | `Review/Examples.lean`, all by `decide`/`simp` |
| Corollaries 1–2 (C(6) = 3; unions of classes) | missing | low priority | — |
| Table 1 numerics (L up to 10⁸) | — | out of scope for kernel checking | — |

**Mathematical gaps** (claims of the PDF with no theorem yet): exponent-blindness, the correction theorem, the `lcm` form, minimal-positive packaging, the `S(L)` decomposition, the specializations, and the examples.
**Lean-ergonomics issues** (the claims are proven, the packaging is rough): see §2 and §4.

---

## 2. Architecture

**Layering is clean and one-directional.** `GDTReadingPoint` imports upstream. Upstream is untouched, and nothing is duplicated from GAP. This matches the README's design rule.

**GAP is a leaf adapter today.** Only `ZmodBridge.lean` touches `GAP.*`: four `iff` lemmas about admissibility. Every GDT theorem (period, minimality, count, density) runs on Mathlib alone, so "lifting into Volkan's verified GAP machinery" currently means "admissibility is equivalent to `isUnit`/`isUnitExec`". `GapBridge.lean` (§6) makes GAP part of the statements themselves.

**Housekeeping:**
- The root `GDTReadingPoint.lean` omits `Correction`, so `import GDTReadingPoint` leaves out `correctionFactor` (fixed in the patch).
- `Count.lean` does `import Mathlib.Tactic`, which pulls in all of Mathlib (~7,600 modules) for tactics that are core Lean (`omega`, `simp`, `ac_rfl`). `import Mathlib.Data.Nat.Totient` suffices; I verified the build with it. This is cosmetic while `ZmodBridge` pulls in all of Mathlib anyway.
- `Rset` and `Rrest` are proof plumbing exposed in the public `Params` namespace. The §4 minimality proof makes them unnecessary.
- Stale docs: the `Basic.lean` comment says `d, R, Tmin` are "planned" (they live in `Parameters.lean`), and the README layout lists 5 of 13 files. `SPEC.md` RP0–RP5 would benefit from a status column pointing to declarations, which is essentially the table in §1.
- The CI "Axiomatic Purity Audit" step reruns `lake build`. A real audit is a file of `#print axioms` lines for the headline theorems, with output checked against the allowed list.

---

## 3. Mathematical definitions

| Def | Verdict |
|---|---|
| `radN = ∏ p ∈ N.primeFactors, p` | Correct for `N > 0`; equals Mathlib `UniqueFactorizationMonoid.radical N` (proven). |
| `d = ∏ (N.pf ∩ m.pf)` | Correct; equals `radical (gcd m N)` via `Nat.primeFactors_gcd` (proven). |
| `R = ∏ (N.pf \ m.pf)` | Correct; equals `radN / d` (proven). Products over finsets are the right Lean choice: coprimality and squarefreeness come for free, and the division forms are derived lemmas. |
| `Tmin = m * R` | Correct; equals `lcm m radN` (proven). |
| `Good n := n % m = a % m ∧ Coprime n N` | Correct. It is definitionally `Nat.ModEq m n a ∧ …`, and the proofs `change` into `ModEq` 7 times. A `good_iff` simp lemma (or a `ModEq`-based definition) would remove that. |
| `Admissible a d := Coprime a d` | Correct. Coprimality with `d` is invariant under `a ↦ a % m` because `d ∣ m`, so using `P.a` rather than `P.a % P.m` is sound. |
| `IsPeriod P T := ∀ n : ℕ, Good (n+T) ↔ Good n` | Correct one-sided notion for `n ≥ 1` counting. `T = 0` is trivially a period, hence `Tmin_isLeast` over positive `T`. |
| Windows `[k, k+Tmin)` over ℕ | Correct; `[0, Tmin)` includes `0`, and the uniform window result makes this harmless. The PDF's `S` counts `[1, L]`, provided as `S`. |

**Natural residue representatives:** sound as mathematics, because the class depends only on `a mod m` and so does admissibility (`d ∣ m`). The PDF says "`a` any integer". If the README repeats that claim, add a ~15-line lemma: for `a : ℤ`, take `Params` with `a' := (a % m).toNat`. Then `Good` agrees with `(n : ℤ) ≡ a [ZMOD m] ∧ Coprime n N`, and `Admissible a' d ↔ Int.gcd a d = 1`. This is representation, with no change to the mathematics.

---

## 4. Proof structure (same statements, less code)

All existing proofs are correct and can stay until replacements land.

**`Count.lean` (836 lines):**
- `goodCount_succ`, `goodCount_add_Tmin`, `goodCount_add_mul_Tmin` and `goodCount_eq_zero` (~250 lines: a hand-built cyclic-shift bijection) collapse to Mathlib's `Nat.filter_Ico_card_eq_of_periodic`:
  ```lean
  theorem good_periodic (P) : Function.Periodic (Good P) (Params.Tmin P) :=
    fun n => propext (good_add_Tmin_iff P n)
  theorem goodCount_eq_count (P) (k) : goodCount P k = Nat.count (Good P) (Params.Tmin P) :=
    Nat.filter_Ico_card_eq_of_periodic k _ (Good P) (good_periodic P)
  ```
- The `residuePoint`/`residueImage` parametrization (~450 lines) can be replaced by an explicit-inverse bijection, `Finset.card_nbij'` with `n ↦ n % R` and `r ↦ Nat.chineseRemainder co a r`. The target is `Nat.totient R = #{r ∈ range R | R.Coprime r}`, which holds by `rfl`. Total ≈45 lines (`CountAlt.lean`).
- `good_iff_coprime_R` (on an admissible class, `Good n ↔ n ≡ a [MOD m] ∧ Coprime n R`) is the PDF's central step. It is currently re-derived inline in `Nonempty`, `Minimal`, and `Count`; stating it once removes that duplication. Likewise `0 < R` is proven inline three times.

**`Minimal.lean` (347 lines):** `prime_dvd_period_of_mem_R` faithfully mirrors the PDF's double-CRT witness (≈190 lines). An orbit argument is shorter and proves more:

> Take one good `n`. A period `T` keeps `n + jT` good for all `j`. If a prime `q ∣ N` has `q ∤ T`, then `T` is a unit in `ZMod q`, so `j := (−n·T⁻¹).val` gives `q ∣ n + jT`, contradicting coprimality with `N`.

This gives `q ∣ T` for **every** prime `q ∣ N`, hence `radN ∣ T` (`Finset.prod_primes_dvd`), and `Tmin = lcm m radN ∣ T` by `Nat.lcm_dvd`. `Rset`, `Rrest`, `coprime_q_Rrest`, `R_eq_q_mul_Rrest` and the induction in `R_dvd_period` all disappear (`MinimalAlt.lean`, ≈45 lines of proof). Trade-off: this departs from the PDF's proof text while keeping its statements. If proof-text fidelity is a project goal, keep the original and cite both.

**`Density.lean`:** `density_eq_totient_div_Tmin` and `density_eq_totient_div_mR` are `rfl` restatements of the definition. They are harmless as documentation; the substantive theorem is `goodCount_div_Tmin_eq_density`.

---

## 5. Correction identity: isolated strategy (done)

The ℚ statement became a coercion loop because the arithmetic and the casts were interleaved. The working design separates them:

1. **Exponent-blindness in ℕ** (no division, holds for all `k`):
   `φ(k) · rad k = k · φ(rad k)`.
   Apply Mathlib's `Nat.totient_mul_prod_primeFactors` to `k` and to `rad k`, using `primeFactors (rad k) = primeFactors k` (`Nat.primeFactors_prod`) and cancelling `rad k > 0`. That is 8 lines.
2. **Correction in ℕ:** `φ(R) · φ(d) · N = d · R · φ(N)`.
   This is step 1 at `k = N` plus `rad N = d·R` (`d_mul_R`) and `φ(rad N) = φ(d)φ(R)` (`totient_radN_eq_mul`): a 4-step `calc`, with each step by `ring` or an existing lemma.
3. **One cast-free field lemma** over abstract variables in any field `K`:
   `φR · φd · N = d · R · φN  ⇒  φR/(m·R) = d/φd · (φN/(N·m))`
   via `div_mul_div_comm`, `div_eq_div_iff`, `linear_combination m * h`.
4. **One cast step:** `exact_mod_cast correction_nat P` feeds step 3, and `push_cast` aligns `Tmin`.

The result is `density_eq_correctionFactor_mul_naive : density P = correctionFactor P * naiveDensity P`, with `naiveDensity P := φ(N)/(N·m)`, which is the PDF's own naive prediction. (The form in the hand-off message used `φ(rad N)/rad N`. That is equivalent via exponent-blindness, but the PDF states it with `N`, and that is what is proven.) `density_div_naive_eq_correctionFactor` gives the literal ratio `C = d/φ(d)`.

---

## 6. Recommended next integration

Revised roadmap. ChatGPT's order holds, with two items moved ahead:

1. **Apply the `Params` patch and turn on CI for `GDTReadingPoint`.** This is urgent; until then the development proves nothing about actual parameters.
2. **Concrete PDF examples**, moved earlier because they are the cheapest guard against this class of bug. `Review/Examples.lean` checks both §3.3 examples by `decide`/`simp`, with no `native_decide` (the `Nat.primeFactorsList` simproc handles factorization):
   - `N=18, m=2, a=1`: `d=2`, `R=3`, `Tmin=6`, `18` is a period, `IsLeast {T | 0<T ∧ IsPeriod T} 6`, `S 18 = 6`.
   - `N=5, m=6, a=2`: `gcd(a,m)=2` yet admissible (`d=1`), `R=5`, `Tmin=30`, `S 30 = 4 = φ(5)`, `C = 1`, while `m/φ(m) = 3`.
3. **Spec-conformance identities**: `Review/Conformance.lean` (all done).
4. **Correction theorem**: `Review/Correction.lean` (done; §5).
5. **Deeper GAP bridge**, the step that makes the "lifting into GAP" claim substantive (`Review/GapBridge.lean`, checked):
   ```lean
   theorem good_iff_gap (P) (n) : Good P n ↔
       (ofNat n : ZModnZObj P.m) = ofNat P.a ∧ IsUnit (ofNat n : ZModnZObj P.N)
   theorem good_iff_gap_exec (P) (n) : Good P n ↔
       (ofNat n : ZModnZObj P.m) = ofNat P.a ∧ isUnitExec (ofNat n : ZModnZObj P.N) = true
   theorem card_units_ZModnZObj (n) [NeZero n] : Fintype.card (ZModnZObj n)ˣ = φ n
   theorem goodCount_eq_card_units_gap (P) (hadm) (k) :
       goodCount P k = Fintype.card (ZModnZObj (Params.R P))ˣ
   ```
   This states RP1 for the whole acceptance predicate (GAP's verified `isUnitExec` decides `Good`) and RP3 as "one period contains exactly as many accepted points as GAP's ℤ/Rℤ has units". A natural follow-on is a CRT equivalence `ZModnZObj (m*R) ≃+* ZModnZObj m × ZModnZObj R` (transfer Mathlib's `ZMod.chineseRemainder`), which is the structural reason behind both the period and the count.
6. **Proof simplifications from §4**, optional and best done as separate commits with statements frozen.
7. **Specializations** (Thm 2, 1′, 1) by substitution, plus the integer-`a` wrapper.
8. **README/SPEC**: a PDF claim → Lean declaration → `#print axioms` table, the §1 table with links.

**Ground rules for the implementation loop:** no new APIs beyond what is in Mathlib v4.28.0 and the upstream `GAP.ZModnZObj` file (everything above uses only those); no `sorry`; no `native_decide` (it adds `Lean.ofReduceBool`); and every new structure ships with a concrete inhabitant in `Examples.lean`.
