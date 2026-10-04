# GDT Reading Point

A Lean 4 integration experiment connecting the General Divisor Theorem (GDT)
specification with the formally verified GAP modular-residue machinery in
Volkan Dağlı's `gap-lean4-port`.

## Leading specification

https://antiviolence.ai/gdt.pdf

## Upstream

https://github.com/pCwOrM/gap-lean4-port

This directory is intended to leave the upstream `RequestProject` implementation
unchanged at first. It develops bridge statements by importing and reusing the
verified modular residue, gcd, and invertibility machinery already present in
the GAP port.

**Reading point → bridge → theorem.**

The first target is the GDT admissibility condition

```text
gcd(a, d) = 1
```

and its expression through verified modular invertibility.

## Initial layout

```text
gdt-readingpoint/
├── README.md
├── SPEC.md
├── GDTReadingPoint.lean
└── GDTReadingPoint/
    ├── Basic.lean
    ├── Admissible.lean
    ├── ZmodBridge.lean
    ├── Period.lean
    └── Examples.lean
```

## Design rule

This is not a second copy of the existing General Divisor Theorem Lean
formalization. It is a reading point where the independent GDT specification
meets the existing GAP formal architecture.

The upstream GAP code should remain unchanged until a concrete bridge requires
otherwise.
