# GDT Reading Point — Specification Targets

Leading specification:

https://antiviolence.ai/gdt.pdf

The initial targets are deliberately ordered from the smallest shared object to
the general GDT statements.

| ID | Target | Role |
|---|---|---|
| RP0 | `gcd(a,d)=1` | GDT admissibility |
| RP1 | admissible ↔ modular unit | GAP ↔ GDT bridge |
| RP2 | `Tmin = m * R` | exact period |
| RP3 | count over one period = `φ(R)` | exact count |
| RP4 | density = `φ(R)/(mR)` | exact density |
| RP5 | correction = `d/φ(d)` | density correction |

where

```text
d = rad(gcd(m,N))
R = rad(N) / d
Tmin = mR
```

## Initial implementation policy

1. Reuse upstream GAP modular arithmetic rather than reproving it.
2. Keep upstream source files unchanged initially.
3. Add no `sorry` merely to make target statements appear complete.
4. Record unimplemented theorem targets as specification comments until their
   exact upstream API dependencies are confirmed.
5. Preserve provenance: GAP machinery comes from the upstream project; GDT
   statements come from the independent PDF specification.

## First bridge

The first implemented theorem should connect:

```text
Nat.Coprime a d
```

with the upstream GAP representation of a unit/invertible residue modulo `d`.

Exact constructor and theorem names should be filled in only after confirming
the current upstream API.
