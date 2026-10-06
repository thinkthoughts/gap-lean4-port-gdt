# GDT reading point: review proposals (kernel-checked)

These files accompany `REVIEW.md`. They compiled against this snapshot with the
pinned toolchain (Lean v4.28.0, Mathlib v4.28.0), **after** applying
`0001-gdt-params-fix.patch`. They use 0 `sorry` and 0 `native_decide`; the
axioms are only `propext`, `Classical.choice`, `Quot.sound`.

| File | Contents |
|---|---|
| `0001-gdt-params-fix.patch` | Minimal correctness fix (apply first): `Params` fields `ℕ → Nat`, `autoImplicit = false`, inhabitation guard, `Examples.lean` decide fix, root imports `Correction`, CI builds `GDTReadingPoint`. |
| `VacuityDemo.lean` | Proof (axiom-free) that the current `Params` is empty, and a deliberately false count theorem that type-checks because of it. Fails to compile after the patch, as it should. |
| `Conformance.lean` | `d = radical (gcd m N)`, `radN = radical N`, `R = radN / d`, `Tmin = lcm m radN`, `Tmin_isLeast`, `good_periodic`, `goodCount_eq_count`, PDF counting function `S` with `S_eq : S (q*Tmin + s) = q*φ(R) + S s`, `S_mul_Tmin`, `S_eq_zero_of_not_admissible`. |
| `Correction.lean` | Exponent-blindness `φ(k)·rad k = k·φ(rad k)` and ratio form; `correction_nat`; `density_eq_correctionFactor_mul_naive`; `density_div_naive_eq_correctionFactor`. |
| `MinimalAlt.lean` | Orbit-argument replacement for `prime_dvd_period_of_mem_R`: every prime of `N` divides every period ⇒ `radN ∣ T` ⇒ `Tmin_dvd_period'` via `lcm`. |
| `CountAlt.lean` | `good_iff_coprime_R` (reusable) and a CRT-bijection proof of the per-period count `φ(R)`. |
| `Examples.lean` | PDF §3.3: `N=18, m=2, a=1` (Tmin = 6, 18 a non-minimal period, `S 18 = 6`) and `N=5, m=6, a=2` (admissible with `gcd(a,m)=2`, Tmin = 30, `S 30 = 4`, `C = 1`, the wrong factor `m/φ(m) = 3`). |
| `GapBridge.lean` | `good_iff_gap` / `good_iff_gap_exec` (acceptance stated in `ZModnZObj m`, `ZModnZObj N`), `card_units_ZModnZObj`, `goodCount_eq_card_units_gap`. |
| `ZmodnzLocal.lean` | Scratch only: body-identical copy of upstream `Zmodnz.lean` with `import Mathlib` narrowed, so `GapBridge` could be checked on a 2-core machine without the Mathlib cache. In the repo, import `RequestProject.Gap.Library.Zmodnz` instead and drop this file. |

To adopt a file into `GDTReadingPoint`: rename the module path
(`Review.X` → `GDTReadingPoint.X`), fix imports, and add it to the root import file.
