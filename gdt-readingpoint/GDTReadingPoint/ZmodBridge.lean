import GDTReadingPoint.Admissible

namespace GDTReadingPoint

/-
GAP ↔ GDT bridge target
=======================

This file intentionally contains no guessed upstream identifiers.

After confirming the exact current API in `RequestProject`, import the relevant
GAP modular-residue module here and implement the first bridge:

    Admissible a d
      ↔
    IsUnit (the upstream residue object representing a mod d)

The upstream project already contains verified gcd / modular-invertibility
machinery. The purpose of this file is to reuse that result rather than rebuild
Bézout or inverse theory locally.

Expected proof shape:

1. unfold `Admissible`;
2. rewrite using the upstream theorem characterizing `IsUnit`;
3. normalize the residue object's stored value if necessary;
4. close using `Nat.Coprime`.

No `sorry` is introduced at the scaffold stage.
-/

end GDTReadingPoint
