# The formalized manuscript

The formalization follows *Pretorsion theories and image-closed subcategories* by
Haruhisa Enomoto, [hexagon:2611.00207v1](https://hexagonmath.org/2611.00207v1) (version 1, November 10, 2026,
CC BY 4.0). The formalization was made from the version prepared for submission on
November 8, 2026; the TeX source posted as hexagon:2611.00207v1 is byte-identical to
it (the `main.tex` hash below, checked on November 11, 2026). The PDF hash below is
that of the author's build; Hexagon's own PDF build differs in its bytes.

Statement numbers and `main.tex` line numbers in the
[correspondence](PAPER-CORRESPONDENCE.md) refer to this version, a single-file
LaTeX source. Statement numbers come from a three-pass `pdflatex` build.

| File | SHA-256 |
| --- | --- |
| `main.tex` | `798e9fe07db9d0c1527fb714b5947ac970fc7937b9eb791352ab6db6fad5d864` |
| PDF | `36dd485dc1d8519752dd7fa77b9a8ca60044e954d0642f5620ed93b5cad572f5` |

The cited inputs used by the formalized results are proved: the closure properties of
pretorsion theories (Campanini–Fedele–Yıldırım), the properties of prekernels and
precokernels and the reconstruction formulas (Facchini–Finocchiaro–Gran), the
properties of traces and rejects and the image closure (Auslander–Smalø), the
anti-exchange property of quotient and submodule closure (from the author's
equidistribution paper), and the facts about convex geometries (Edelman–Jamison).
The identities `B_m(1,1) = g_{2m+2}` and `C_m(1,1) = H_{2m+1}` with the Genocchi and
median Genocchi numbers are classical and are not formalized; Theorem B is formalized
in terms of the Gandhi polynomials.

Some arguments differ from the paper; they are summarized in
[`proofs/`](proofs/README.md).
