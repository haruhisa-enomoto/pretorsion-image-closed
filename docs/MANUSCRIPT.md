# The formalized manuscript

The formalization follows *Pretorsion theories and image-closed subcategories* by
Haruhisa Enomoto, in the version prepared for submission on November 8, 2026. It has
not yet been posted to arXiv or Hexagon; this record will name the public version
when there is one.

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
