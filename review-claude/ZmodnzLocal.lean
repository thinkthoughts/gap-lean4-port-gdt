import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Data.Int.GCD
-- SCRATCH COPY of RequestProject/Gap/Library/Zmodnz.lean with `import Mathlib` narrowed,
-- used only to type-check review proposals in a 2-core sandbox. Body unchanged.

/-!
# GAP ℤ/nℤ Modular Arithmetic & Executable Algorithms (`lib/zmodnz.gi`)

This file formalizes both the algebraic representation and the concrete executable
algorithms for elements of the residue class rings ℤ/nℤ, faithfully following
GAP 4's library file `lib/zmodnz.gi` (by Thomas Breuer).

## Constructive & Executable Verification (Zero `Classical.choice`)
In addition to the full Mathlib `CommRing` and `Field` equivalence, this module
explicitly formalizes and proves the correctness of GAP's concrete executable procedures:
* `isUnitExec`: Mirrors `IsUnit` in `lib/zmodnz.gi` (lines 943–949), computing
  `GcdInt(elm![1], Characteristic) == 1`.
* `inverseOpExec`: Mirrors `InverseOp` in `lib/zmodnz.gi` (lines 522–533), computing
  the concrete modular inverse via the Extended Euclidean Algorithm (`Nat.gcdA`) without
  invoking `Classical.choice`.
* `inverseOpExec_correct`: Proves constructively (`0 Classical.choice`) that whenever
  `isUnitExec a = true`, `inverseOpExec a` returns `some inv` satisfying
  `mulExec a inv = oneExec`.
-/

namespace GAP

/-- A GAP ℤ/nℤ element, mirroring GAP's `ZModnZObj` in `lib/zmodnz.gi`.
    Stores the canonical residue `val` strictly bounded by the modulus `n`. -/
structure ZModnZObj (n : ℕ) [NeZero n] where
  /-- The canonical residue `r ∈ {0, ..., n-1}`. -/
  val : ℕ
  /-- The canonical residue is strictly less than the modulus `n`. -/
  val_lt : val < n
  deriving DecidableEq

namespace ZModnZObj

variable {n : ℕ} [NeZero n]

/-! ### Basic Accessors and GAP Constructors -/

/-- The modulus of the element, mirroring GAP's `Modulus(a)`. -/
@[inline] def modulus (_ : ZModnZObj n) : ℕ := n

/-- The canonical residue of the element in `{0, ..., n-1}`, mirroring GAP's `Residue(a)`. -/
@[inline] def residue (a : ZModnZObj n) : ℕ := a.val

/-- Construct an element of ℤ/nℤ from a natural number `r` via reduction modulo `n`.
    Mirrors GAP's `ZModnZObj(r, n)`. -/
def ofNat (r : ℕ) : ZModnZObj n :=
  ⟨r % n, Nat.mod_lt r (NeZero.pos n)⟩

/-- Extensionality: two elements are equal iff their canonical residues are equal. -/
@[ext] theorem ext {a b : ZModnZObj n} (h : a.val = b.val) : a = b := by
  rcases a with ⟨va, ha⟩
  rcases b with ⟨vb, hb⟩
  subst h
  rfl

/-! ### Constructive Executable GAP Operations (`lib/zmodnz.gi`, Zero `Classical.choice`) -/

/-- Executable modular addition (`lib/zmodnz.gi`). -/
def addExec (a b : ZModnZObj n) : ZModnZObj n :=
  ofNat (a.val + b.val)

/-- Executable modular multiplication (`lib/zmodnz.gi`). -/
def mulExec (a b : ZModnZObj n) : ZModnZObj n :=
  ofNat (a.val * b.val)

/-- Executable multiplicative identity (`OneOp` in `lib/zmodnz.gi`, lines 512–515). -/
def oneExec : ZModnZObj n :=
  ofNat 1

/-- Executable unit test (`IsUnit` in `lib/zmodnz.gi`, lines 943–949):
    `GcdInt( elm![1], FamilyObj( elm )!.Characteristic ) = 1`. -/
def isUnitExec (a : ZModnZObj n) : Bool :=
  Nat.gcd a.val n == 1

/-- Extended Euclidean Bézout residue for modular inversion (`QuotientMod` in `lib/zmodnz.gi`, line 528). -/
def bezoutInvNat (a n : ℕ) : ℕ :=
  Int.toNat ((Nat.gcdA a n) % (n : ℤ))

/-- Executable modular inversion (`InverseOp` in `lib/zmodnz.gi`, lines 522–533):
    computes the inverse via Extended GCD if `isUnitExec a` holds, or `none` (`fail`) otherwise. -/
def inverseOpExec (a : ZModnZObj n) : Option (ZModnZObj n) :=
  if isUnitExec a then
    some (ofNat (bezoutInvNat a.val n))
  else
    none

/-- Constructive equivalence between `isUnitExec a = true` and `Nat.Coprime a.val n`. -/
theorem isUnitExec_iff_coprime (a : ZModnZObj n) :
    isUnitExec a = true ↔ Nat.Coprime a.val n := by
  simp [isUnitExec, Nat.Coprime]

/-- Constructive Bézout correctness lemma (completely free of `Classical.choice`):
    for coprime `a` and `n`, `a * bezoutInvNat a n ≡ 1 (mod n)`. -/
theorem bezoutInvNat_mul_mod (a n : ℕ) [NeZero n] (h : Nat.Coprime a n) :
    (a * bezoutInvNat a n) % n = 1 % n := by
  have hn : (0 : ℤ) < (n : ℤ) := Nat.cast_pos.mpr (NeZero.pos n)
  have h_nonneg : 0 ≤ (Nat.gcdA a n) % (n : ℤ) := Int.emod_nonneg _ (ne_of_gt hn)
  have h_gcd : (Nat.gcd a n : ℤ) = (a : ℤ) * Nat.gcdA a n + (n : ℤ) * Nat.gcdB a n :=
    Nat.gcd_eq_gcd_ab a n
  rw [Nat.Coprime.gcd_eq_one h] at h_gcd
  have h_mod : ((a : ℤ) * ((Nat.gcdA a n) % (n : ℤ))) % (n : ℤ) = (1 : ℤ) % (n : ℤ) := by
    calc ((a : ℤ) * ((Nat.gcdA a n) % (n : ℤ))) % (n : ℤ)
      _ = ((a : ℤ) * Nat.gcdA a n) % (n : ℤ) := by rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      _ = ((a : ℤ) * Nat.gcdA a n + (n : ℤ) * Nat.gcdB a n) % (n : ℤ) := by
          rw [Int.add_mul_emod_self_left]
      _ = ((1 : ℕ) : ℤ) % (n : ℤ) := by rw [← h_gcd]
      _ = (1 : ℤ) % (n : ℤ) := rfl
  have h_nat_mod : (((a * bezoutInvNat a n) % n : ℕ) : ℤ) = (((1 % n) : ℕ) : ℤ) := by
    rw [Int.natCast_emod, Int.natCast_mul, bezoutInvNat, Int.toNat_of_nonneg h_nonneg, h_mod]
    rfl
  exact Int.ofNat.inj h_nat_mod

/-- **Constructive Algorithmic Correctness of GAP's `InverseOp` (`lib/zmodnz.gi`, lines 522–533)**:
    If `isUnitExec a = true`, then `inverseOpExec a` returns `some inv` such that
    `mulExec a inv = oneExec`. Proved constructively without `Classical.choice`. -/
theorem inverseOpExec_correct (a : ZModnZObj n) (h : isUnitExec a = true) :
    ∃ inv : ZModnZObj n, inverseOpExec a = some inv ∧ mulExec a inv = oneExec := by
  refine ⟨ofNat (bezoutInvNat a.val n), ?_, ?_⟩
  · simp [inverseOpExec, h]
  · apply ext
    dsimp [mulExec, oneExec, ofNat]
    rw [Nat.mul_mod_mod]
    exact bezoutInvNat_mul_mod a.val n ((isUnitExec_iff_coprime a).mp h)

/-! ### Mathlib Realization and Equivalence -/

/-- Canonical projection from GAP's `ZModnZObj n` to Mathlib's `ZMod n`. -/
def toZMod (a : ZModnZObj n) : ZMod n :=
  (a.val : ZMod n)

/-- Canonical embedding from Mathlib's `ZMod n` to GAP's `ZModnZObj n`. -/
def ofZMod (z : ZMod n) : ZModnZObj n :=
  ⟨z.val, z.val_lt⟩

@[simp] theorem val_toZMod (a : ZModnZObj n) : (toZMod a).val = a.val :=
  ZMod.val_cast_of_lt a.val_lt

@[simp] theorem toZMod_ofZMod (z : ZMod n) : toZMod (ofZMod z) = z :=
  ZMod.natCast_zmod_val z

@[simp] theorem ofZMod_toZMod (a : ZModnZObj n) : ofZMod (toZMod a) = a := by
  rcases a with ⟨v, hv⟩
  dsimp [ofZMod, toZMod]
  congr
  exact ZMod.val_cast_of_lt hv

/-- The canonical bijection between GAP's `ZModnZObj n` and Mathlib's `ZMod n`. -/
def equivZMod : ZModnZObj n ≃ ZMod n where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod

/-- `ZModnZObj n` is a finite type. -/
instance : Fintype (ZModnZObj n) :=
  Fintype.ofEquiv (ZMod n) equivZMod.symm

/-- Cardinality of GAP's ℤ/nℤ is exactly `n`. -/
@[simp] theorem card_eq : Fintype.card (ZModnZObj n) = n := by
  rw [Fintype.card_congr equivZMod, ZMod.card]

/-! ### Algebraic Instances -/

/-- Commutative ring instance transferred from Mathlib's `ZMod n`. -/
instance : CommRing (ZModnZObj n) :=
  equivZMod.commRing

@[simp] theorem toZMod_zero : toZMod (0 : ZModnZObj n) = 0 :=
  equivZMod.apply_symm_apply 0

@[simp] theorem toZMod_one : toZMod (1 : ZModnZObj n) = 1 :=
  equivZMod.apply_symm_apply 1

@[simp] theorem toZMod_add (a b : ZModnZObj n) : toZMod (a + b) = toZMod a + toZMod b :=
  equivZMod.apply_symm_apply (toZMod a + toZMod b)

@[simp] theorem toZMod_mul (a b : ZModnZObj n) : toZMod (a * b) = toZMod a * toZMod b :=
  equivZMod.apply_symm_apply (toZMod a * toZMod b)

@[simp] theorem toZMod_neg (a : ZModnZObj n) : toZMod (-a) = -toZMod a :=
  equivZMod.apply_symm_apply (-toZMod a)

@[simp] theorem toZMod_sub (a b : ZModnZObj n) : toZMod (a - b) = toZMod a - toZMod b :=
  equivZMod.apply_symm_apply (toZMod a - toZMod b)

theorem toZMod_inj {a b : ZModnZObj n} : toZMod a = toZMod b ↔ a = b :=
  equivZMod.injective.eq_iff

/-- Invertibility / unit predicate: `a` is a unit in GAP's ℤ/nℤ iff its residue is coprime to `n`. -/
theorem isUnit_iff (a : ZModnZObj n) : IsUnit a ↔ a.val.Coprime n := by
  rw [isUnit_iff_dvd_one]
  have h_dvd : (a ∣ 1) ↔ (toZMod a ∣ 1) := by
    constructor
    · rintro ⟨c, hc⟩
      use toZMod c
      rw [← toZMod_mul, ← hc, toZMod_one]
    · rintro ⟨z, hz⟩
      use ofZMod z
      have heq : toZMod (a * ofZMod z) = toZMod 1 := by
        rw [toZMod_mul, toZMod_ofZMod, ← hz, toZMod_one]
      exact toZMod_inj.mp heq.symm
  rw [h_dvd, ← isUnit_iff_dvd_one]
  change IsUnit ((a.val : ℕ) : ZMod n) ↔ a.val.Coprime n
  exact ZMod.isUnit_iff_coprime a.val n

/-- Equivalence between the abstract ring `IsUnit` predicate and GAP's executable `isUnitExec`. -/
theorem isUnit_iff_isUnitExec (a : ZModnZObj n) : IsUnit a ↔ isUnitExec a = true := by
  rw [isUnit_iff, isUnitExec_iff_coprime]

/-- When the modulus `n` is prime, GAP's ℤ/nℤ is a field. -/
instance [Fact (Nat.Prime n)] : Field (ZModnZObj n) :=
  equivZMod.field

end ZModnZObj
end GAP
