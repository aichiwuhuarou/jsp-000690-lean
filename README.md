# JSP-000690 in Lean 4: a critically 3-chromatic 3-uniform hypergraph of minimum degree 7

Justin Sun Prize problem bank entry **JSP-000690**: *Is there a three-uniform,
three-chromatic-critical hypergraph with minimum degree at least seven?*

The problem (Erdős–Lovász) was resolved affirmatively under the chromatic
interpretation by **Ruiliang Li** (arXiv:2512.24850, 2025) via an explicit
construction. This repository machine-checks the answer in **pure Lean 4 core
(no mathlib, no axioms)**:

> **Theorem (`Jsp690.jsp_000690`).** The hypergraph `edges`, consisting of
> 22 triples on 9 vertices (vertex set {0,…,8}), is 3-uniform, has minimum
> degree 7 (degree 10 at vertex 0, degree 7 at the other eight vertices),
> admits no proper 2-colouring but a proper 3-colouring (chromatic number 3),
> and becomes 2-colourable after deleting any single edge or any single
> vertex.

Every claim is verified by the Lean kernel via `decide`: the 2-colourability
search enumerates all 512 colourings; criticality searches re-derive the
witness colourings listed in Appendix B of the paper; degrees are counted
directly. The kernel reports: **`'jsp_000690' does not depend on any
axioms`** (auditable via `Jsp690/Audit.lean`).

## Building

Requires only [elan](https://elan.lean-lang.org) with the pinned toolchain
(`lean-toolchain`; currently Lean 4.33.0). No network or package downloads:

```sh
lake build          # ≈ 4 seconds
lake env lean Jsp690/Audit.lean   # prints the axiom audit
```

## Attribution

* **Mathematical solution**: Ruiliang Li, *On an Erdős–Lovász problem:
  3-critical 3-graphs of minimum degree 7*, arXiv:2512.24850 (2025).
  Edge set: equation (5); witness colourings: Appendix B.
* **Lean formalization**: AI-assisted (GLM, via the ZCode agent), directed
  by @aichiwuhuarou, September 2026. All code is original to this
  repository.

## License

Apache License 2.0.
