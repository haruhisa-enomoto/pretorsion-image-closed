# Paper correspondence

One row per numbered statement of [the paper](MANUSCRIPT.md), in source order,
plus the cited inputs. Line numbers refer to `main.tex` of the version described in
[MANUSCRIPT.md](MANUSCRIPT.md). Status words: `defined`; `covered`;
`covered (different route)`; `not needed`; `not formalized`; `expository`;
`out of scope`.

Sections 2–4 are proved for an abelian category with a length function
(`HasLength`); `mod Λ` and the representations of the linear quiver are instances.
Lean names are in namespace `PretorsionImageClosed`. Paths are relative to
`PretorsionImageClosed/`. Arguments that differ from the paper are summarized in
[proofs/](proofs/README.md).

| No. | Kind | Label | Source | Status | Lean |
|---|---|---|---|---|---|
| Thm A | theorem | `thm:intro-main` | `main.tex:224` | covered | `theoremA` (`MainTheorems.lean`), via Theorem 4.4 |
| (1.1) | equation | `eq:genocchi-egf` | `main.tex:336` | out of scope (the classical definition of Genocchi numbers, used only in the introduction) | — |
| 1.1 | definition | `def:gandhi-polynomials` | `main.tex:347` | covered: `IsDelta`, `IsGandhiFirst`, `IsGandhiSecond` (statement); existence and uniqueness in `Gandhi/Delta.lean` (`gandhiFirst`, `gandhiSecond`, `IsGandhiFirst.eq`, `IsGandhiSecond.eq`) | `Statement.lean`, `Gandhi/Delta.lean` |
| (1.2) | equation | `eq:intro-delta` | `main.tex:349` | covered (as the relation `IsDelta`; uniqueness `IsDelta.unique`, existence `exists_isDelta`) | `Statement.lean`, `Gandhi/Delta.lean` |
| (1.3) | equation | `eq:intro-B` | `main.tex:356` | covered | `IsGandhiFirst` |
| (1.4) | equation | `eq:intro-C` | `main.tex:357` | covered | `IsGandhiSecond` |
| Thm B | theorem | `thm:intro-enumeration` | `main.tex:377` | covered | `theoremBPretorsion`, `theoremBImageClosed` (`MainTheorems.lean`) |
| 2.1 | definition | `def:image-closed` | `main.tex:483` | defined | `Statement.IsImageClosed` (`Statement.lean`), `Subcategory.IsQuotientClosed`, `Subcategory.IsSubobjectClosed` (`Subcategories/Basic.lean`); `L_quot`, `L_sub`, `L_im` are the corresponding predicates on `Statement.Subcategory` |
| (2.1) | equation | `eq:image-in-intersection` | `main.tex:498` | covered | `Subcategory.IsImageClosed.inf_of_closed` (`Subcategories/Basic.lean`) |
| 2.2 | definition | `def:pretorsion` | `main.tex:507` | defined | `Statement.IsTrivial`, `IsPrekernel`, `IsPrecokernel`, `IsShortPreexact`, `IsPretorsionTheory` (`Statement.lean`), for an arbitrary category |
| 2.3 | proposition | `prop:pretorsion-closure` | `main.tex:557` | covered (closure under finite direct sums and summands is part of the `Subcategory` convention) | `IsPretorsionTheory.isQuotientClosed`, `IsPretorsionTheory.isSubobjectClosed` (`Pretorsion/Basic.lean`) |
| (2.2) | equation | `eq:PT-order` | `main.tex:570` | defined | `Statement.PretorsionTheory`, `PretorsionTheory.LE` (`Statement.lean`) |
| 2.4 | definition | `def:torsion-pair` | `main.tex:578` | defined | `IsTorsionPair` (`Pretorsion/TorsionPairs.lean`) |
| 2.5 | proposition | `prop:zero-middle-torsion` | `main.tex:591` | covered | `isTorsionPair_iff` (`Pretorsion/TorsionPairs.lean`) |
| 2.6 | example | `ex:A1-pretorsion` | `main.tex:609` | expository | — |
| 2.7 | definition | `def:trace-reject` | `main.tex:635` | defined (as the largest subobject in `T`, resp. the smallest subobject with quotient in `F`; the sum-of-images and intersection-of-kernels descriptions are `trace_le_iff` and `le_reject_iff`) | `Subcategory.trace`, `Subcategory.reject` (`Subcategories/Trace.lean`) |
| 2.8 | remark | `rem:duality` | `main.tex:648` | covered (for the opposite category instead of `Hom_k(-, k)`) | `IsPretorsionTheory.op`, `IsPretorsionTheory.unop`, `PretorsionTheory.op_LE_op_iff` (`Pretorsion/Duality.lean`) |
| 2.9 | lemma | `lem:finite-intersection` | `main.tex:671` | covered (different route: the finiteness enters through the length function `HasLength`, which gives maximal and minimal subobjects) | `HasLength`, `Subobject.exists_maximal_of_nonempty`, `Subobject.exists_minimal_of_nonempty` (`Length/Basic.lean`) |
| 2.10 | proposition | `prop:trace-reject-properties` | `main.tex:684` | covered: (1) `le_trace`, `prop_trace`; (2) `reject_le`, `prop_cokernel_reject`; (3) `trace_eq_top_iff`, `reject_eq_bot_iff`; (4) `trace_biprod`, `reject_biprod`; (5) `push_trace_le`, `push_reject_le` | `Subcategories/Trace.lean` |
| (2.3) | equation | `eq:trace-reject-sums` | `main.tex:693` | covered | `trace_biprod`, `traceBiprodIso`, `reject_biprod` |
| 2.11 | lemma | `lem:relative-mono-epi` | `main.tex:733` | covered | `IsPrekernel.mono`, `IsPrecokernel.epi` (`Pretorsion/Basic.lean`) |
| 2.12 | theorem | `thm:trace-reject` | `main.tex:747` | covered; the condition (2.4) is `TraceRejectCondition` (with `r(X) ≤ t(X)` explicit) | `isPretorsionTheory_iff_traceRejectCondition`, `TraceRejectCondition.prop_image`, `TraceRejectCondition.isPrekernel`, `TraceRejectCondition.isPrecokernel` (`Pretorsion/TraceReject.lean`) |
| (2.4) | equation | `eq:trace-reject` | `main.tex:751` | defined | `TraceRejectCondition` (`Pretorsion/TraceReject.lean`) |
| 2.13 | corollary | `cor:reconstruction` | `main.tex:849` | covered | `IsPretorsionTheory.prop_iff_prop_trace`, `IsPretorsionTheory.prop_iff_prop_cokernel_reject` (`Pretorsion/TraceReject.lean`) |
| (2.5) | equation | `eq:reconstruction` | `main.tex:851` | covered | as Corollary 2.13 |
| 3.1 | lemma | `lem:trace-quotient` | `main.tex:917` | not needed: the Lean proof of Proposition 3.2 divides by one reject at a time (`traceRejectCondition_of_quotient_reject`) | — |
| 3.2 | proposition | `prop:partner-intersection` | `main.tex:972` | covered (different proof: one reject at a time with `IsShortPreexact.of_quotient`; arbitrary families by a finite subfamily with maximal reject) | `isPretorsionTheory_inf`, `isPretorsionTheory_iInf` (`Pretorsion/Partners.lean`) |
| (3.1) | equation | `eq:transport` | `main.tex:994` | replaced by `IsShortPreexact.of_quotient` | `Pretorsion/Lifting.lean` |
| 3.3 | lemma | `lem:one-sided` | `main.tex:1068` | covered (via Lemma 3.7) | `isPretorsionTheory_of_reject_trace` (`Pretorsion/Partners.lean`) |
| 3.4 | lemma | `lem:trace-trapping` | `main.tex:1105` | covered | `prop_of_prop_cokernel_reject` (`Pretorsion/Partners.lean`) |
| 3.5 | proposition | `prop:lower-bound` | `main.tex:1125` | covered (via Lemma 3.7, as in the proof of Proposition 3.8) | `isPretorsionTheory_iInf_left` (`Pretorsion/Partners.lean`) |
| 3.6 | theorem | `thm:PT-lattice` | `main.tex:1161` | covered | `completeLattice` (`MainTheorems.lean`); instance and formulas in `Pretorsion/Lattice.lean` |
| (3.2) | equation | `eq:PT-meet` | `main.tex:1164` | covered | `PretorsionTheory.sInf_T_prop`, `PretorsionTheory.sInf_F_prop` |
| (3.3) | equation | `eq:PT-join` | `main.tex:1169` | covered (by duality, `Pretorsion/Duality.lean`) | `PretorsionTheory.sSup_T_prop`, `PretorsionTheory.sSup_F_prop` |
| 3.7 | lemma | `lem:realization-criterion` | `main.tex:1201` | covered (with `K = r_F(t(X))` in place of `r_Z(t(X))`) | `isPretorsionTheory_of_realization` (`Pretorsion/Realization.lean`) |
| (3.4) | equation | `eq:realization-F` | `main.tex:1205` | covered | hypothesis `hF'` of `isPretorsionTheory_of_realization` |
| (3.5) | equation | `eq:realization-T` | `main.tex:1208` | covered | hypothesis `hT'` of `isPretorsionTheory_of_realization` |
| (3.6) | equation | `eq:realization-trace` | `main.tex:1236` | covered | the step `hb` inside the proof of `isPretorsionTheory_of_realization` |
| 3.8 | proposition | `prop:fixed-intersection-lattice` | `main.tex:1258` | covered (joins by duality) | `PretorsionTheory.sInf_middle`, `PretorsionTheory.sSup_middle` (`Pretorsion/FixedMiddle.lean`) |
| 3.9 | corollary | `cor:torsion-sublattice` | `main.tex:1318` | covered | `IsTorsion.sInf`, `IsTorsion.sSup`, `isTorsion_bot`, `isTorsion_top`, `IsTorsion.le_iff`, `IsTorsion.eq_of_T_eq` (`Pretorsion/TorsionPairs.lean`) |
| 4.1 | definition | `def:gen-cogen` | `main.tex:1347` | defined (for a subcategory, as quotients and subobjects of its objects, since it is closed under finite direct sums) | `Statement.Gen`, `Statement.Cogen` (`Statement.lean`) |
| 4.2 | example | `ex:semisimple-middle` | `main.tex:1357` | expository | — |
| 4.3 | construction | `def:middle-endpoints` | `main.tex:1377` | defined | `upperFirst`, `lowerSecond` (`Realizations/TheoremA.lean`) |
| 4.4 | theorem | `thm:image-middle` | `main.tex:1396` | covered | `isImageClosed_iff_eq_gen_inf_cogen`, `isImageClosed_iff_exists_pretorsionTheory`, `isPretorsionTheory_upperFirst_lowerSecond`, `PretorsionTheory.isImageClosed_middle` (`Realizations/TheoremA.lean`); `theoremA` (`MainTheorems.lean`) proves `Statement.TheoremA` |
| (4.1) | equation | `eq:Tplus-intersection` | `main.tex:1463` | covered | `upperFirst_inf_cogen` (`Realizations/TheoremA.lean`) |
| 4.5 | corollary | `cor:greatest-realization` | `main.tex:1510` | covered | `greatestRealization`, `le_greatestRealization` (`Realizations/TheoremA.lean`) |
| 4.6 | construction | `def:dual-middle-endpoints` | `main.tex:1537` | covered (different route: obtained as the dual of Construction 4.3 in the opposite category; the explicit formulas are not stated) | `leastRealization` (`Realizations/LeastRealization.lean`) |
| 4.7 | corollary | `cor:least-realization` | `main.tex:1546` | covered (the complete lattice `PT_Z` is Proposition 3.8 with the least and greatest elements below) | `realization_bounds`, `isLeast_leastRealization`, `isGreatest_greatestRealization`, `leastRealization_middle` |
| 4.8 | definition | `def:image-closure` | `main.tex:1576` | defined (as `Gen Z ⊓ Cogen Z`) | `Statement.Gen`, `Statement.Cogen` |
| 4.9 | corollary | `cor:image-closure` | `main.tex:1584` | covered | `isImageClosed_gen_inf_cogen`, `le_gen_inf_cogen`, `gen_inf_cogen_le`, with `isImageClosed_iff_eq_gen_inf_cogen` (`Realizations/LeastRealization.lean`) |
| 4.10 | definition | `def:convex-geometry` | `main.tex:1608` | defined (adapted from the equidistribution formalization) | `SetClosure.IsFinitary`, `SetClosure.IsAntiExchange`, `SetClosure.IsConvexGeometry`, `SetClosure.extremePoints` (`ConvexGeometry/Basic.lean`) |
| (4.2) | equation | `eq:three-closures` | `main.tex:1630` | covered | `IndecomposableSkeleton.qSet`, `IndecomposableSkeleton.sSet` with `mem_qSet_iff`, `mem_sSet_iff` (`IndecomposableClosures/Subcategories.lean`) |
| (4.3) | equation | `eq:icl-on-subsets` | `main.tex:1634` | covered | `IndecomposableSkeleton.iClosure`, `iClosure_apply`, `mem_iClosure_iff` (`IndecomposableClosures/ImageClosure.lean`) |
| 4.11 | theorem | `thm:icl-convex` | `main.tex:1653` | covered | `theorem_4_11` (`IndecomposableClosures/FiniteDimensionalAlgebras.lean`); `iClosure_isFinitary`, `iClosure_isClosed_empty`, `iClosure_isAntiExchange`, `isImageClosed_iff_isClosed_indOf`, `imageClosedOrderIso` (`IndecomposableClosures/ImageClosure.lean`) |
| 4.12 | definition | `def:splitting-projective` | `main.tex:1699` | defined | `IsSplittingProjective`, `IsSplittingInjective` (`IndecomposableClosures/ImageClosure.lean`) |
| 4.13 | proposition | `prop:extreme-points` | `main.tex:1713` | covered | `not_mem_qClosure_sdiff_iff`, `not_mem_sClosure_sdiff_iff`, `extremePoints_iff_isImageClosed`, `extremePoints_iff_splitting` (`IndecomposableClosures/ImageClosure.lean`) |
| 4.14 | corollary | `cor:LI-structure` | `main.tex:1773` | covered | (1) `isGLB_iInf`, `isLUB_join`; (2) `iClosure_splitting_eq`, `splitting_subset`; (3) `exists_sdiff_eq_singleton_of_covby`, `ncard_of_covby` (`IndecomposableClosures/ImageClosure.lean`) |
| 5.1 | definition | `def:interval-board` | `main.tex:1824` | defined (the convention `M_{a,a-1} = 0` is `isZero_interval_of_lt`) | `LinearQuiver.interval` (`LinearQuiver/Interval.lean`) |
| 5.2 | proposition | `prop:interval-hom` | `main.tex:1899` | covered: coordinates, the naturality equation and the vanishing conditions give the one-dimensional Hom space (`eq_scalarHom_comp_canonicalHom`, `coord_eq_zero_of_lt`, `coord_eq_zero_of_lt'`); the image is `imageSubobject_canonicalHom` | `LinearQuiver/Hom.lean`, `LinearQuiver/Subobjects.lean` |
| (5.1) | equation | `eq:interval-quot-sub` | `main.tex:1933` | covered: `eq_bot_or_eq_suffix` (subobjects are suffixes), `eq_and_le_of_mono`, `eq_and_le_of_epi` | `LinearQuiver/Subobjects.lean`, `LinearQuiver/Indecomposables.lean` |
| 5.3 | lemma | `lem:summand-reduction` | `main.tex:1954` | covered | `epi_or_epi_of_epi_biprod_desc`, `mono_or_mono_of_mono_biprod_lift` (`LinearQuiver/SummandReduction.lean`) |
| 5.4 | definition | `def:interval-family` | `main.tex:1984` | defined (as a property of the subcategory) | `LinearQuiver.IntersectionClosed` (`LinearQuiver/ImageClosed.lean`) |
| 5.5 | theorem | `thm:intersection-criterion` | `main.tex:1998` | covered | `isImageClosed_iff_intersectionClosed` (`LinearQuiver/ImageClosed.lean`) |
| 5.6 | example | `ex:A2-image` | `main.tex:2048` | expository | — |
| 5.7 | example | `ex:A3-obstruction` | `main.tex:2061` | expository | — |
| 6.1 | proposition | `prop:staircase` | `main.tex:2130` | covered: `isQuotientClosed_iff`, `isSubobjectClosed_iff`, `quotientClosedEquiv`, `subobjectClosedEquiv`, `RowCutoff.subcategory_le_iff`, `ColCutoff.subcategory_le_iff` (0-indexed vertices: the Lean `β a` equals the manuscript `β_a`, the Lean `α d` equals `α_d - 1`) | `LinearQuiver/Cutoffs.lean` |
| (6.1) | equation | `eq:T-beta` | `main.tex:2141` | covered | `RowCutoff.prop_interval_iff` |
| (6.2) | equation | `eq:F-alpha` | `main.tex:2144` | covered | `ColCutoff.prop_interval_iff` |
| 6.2 | definition | `def:row-column-cutoff` | `main.tex:2166` | defined | `RowCutoff`, `ColCutoff`, `rowCutoff`, `colCutoff` (`LinearQuiver/Cutoffs.lean`) |
| (6.3) | equation | `eq:E-d` | `main.tex:2193` | not needed: the Lean criterion and its proof use `d < β a` directly | — |
| 6.3 | lemma | `lem:interval-trace-reject` | `main.tex:2199` | covered: `trace_interval_eq_suffix`, `trace_interval_eq_bot`, `reject_interval_eq_suffix`, `reject_interval_eq_top` | `LinearQuiver/IntervalTraceReject.lean` |
| (6.4) | equation | `eq:s-d` | `main.tex:2241` | not needed: the Lean criterion is (6.4), not the reformulation (6.5) | — |
| 6.4 | example | `ex:earlier-row-failure` | `main.tex:2258` | expository | — |
| 6.5 | theorem | `thm:staircase-pair` | `main.tex:2279` | covered | `isPretorsionTheory_iff_criterion`, `pretorsionEquiv` (`LinearQuiver/CutoffCriterion.lean`) |
| (6.5) | equation | `eq:pair-criterion` | `main.tex:2284` | covered (as the definition `ColumnCriterion`) | `LinearQuiver/CutoffCriterion.lean` |
| (6.6) | equation | `eq:allowed-alpha` | `main.tex:2290` | not stated separately: the Lean criterion is (6.4) itself | — |
| 6.6 | remark | `rem:fixed-beta-chains` | `main.tex:2296` | expository | — |
| 6.7 | example | `ex:A2-partners` | `main.tex:2307` | expository | — |
| 6.8 | example | `ex:A3-cutoffs` | `main.tex:2349` | expository | — |
| (6.7) | equation | `eq:cutoff-earlier-row` | `main.tex:2428` | covered (Step 1 of the proof) | `beta_lt_of_criterion` |
| 6.9 | example | `ex:coordinate-operations` | `main.tex:2594` | expository | — |
| 7.1 | definition | `def:pretorsion-statistics` | `main.tex:2619` | defined | `Statement.rho`, `Statement.pretorsionWeight`; in cutoff coordinates `RowCutoff.rowsReaching`, `middleCount`, `cpWeight` (`LinearQuiver/CutoffWeights.lean`) |
| (7.1) | equation | `eq:pret-b` | `main.tex:2621` | covered | `rho_subcategory`, `rho_eq` |
| (7.2) | equation | `eq:column-middle-size` | `main.tex:2644` | covered (as `colCount`; the column-`n` count of an extension is `colCount_glue_last`) | `LinearQuiver/CutoffWeights.lean`, `LinearQuiver/CutoffRestriction.lean` |
| (7.3) | equation | `eq:A1-pretorsion-weight` | `main.tex:2661` | not formalized separately (an instance of Theorem 7.5) | — |
| 7.2 | lemma | `lem:restriction-extension` | `main.tex:2691` | covered: `CutoffPair.restrict`, `glue`, `restrict_glue`, `glue_contOf_colOf`, `contOf_glue`, `colOf_glue`, `middleCount_glue` | `LinearQuiver/CutoffRestriction.lean` |
| (7.4) | equation | `eq:q-integer` | `main.tex:2729` | not needed: the Lean proof sums over subsets instead of using `q`-integers | — |
| (7.5) | equation | `eq:F-k-def` | `main.tex:2734` | covered (the fibre sum `fiber_sum`) | `LinearQuiver/CutoffRestriction.lean` |
| (7.6) | equation | `eq:binomial-u` | `main.tex:2747` | replaced by the subset induction `psi_insert_max` | `Gandhi/ColumnSum.lean` |
| (7.7) | equation | `eq:geometric-delta` | `main.tex:2755` | covered | `isDelta_X_pow_succ`, `geomSum` (`Gandhi/Delta.lean`) |
| 7.3 | lemma | `lem:first-transfer` | `main.tex:2768` | covered | `psi_eq_geomSum` (`Gandhi/ColumnSum.lean`), `fiber_sum`, `isDelta_cpSum` (`LinearQuiver/CutoffRestriction.lean`) |
| (7.8) | equation | `eq:F-k-delta` | `main.tex:2772` | covered | `psi_eq_geomSum` |
| (7.9) | equation | `eq:first-transfer-sum` | `main.tex:2780` | covered | `isDelta_cpSum` |
| (7.10) | equation | `eq:F-k-expanded` | `main.tex:2838` | replaced: the Lean proof proceeds by induction on the candidate rows (`psi_insert_max`) instead of the binomial double sum | `Gandhi/ColumnSum.lean` |
| (7.11) | equation | `eq:F-k-single-sum` | `main.tex:2853` | replaced (see (7.10)) | — |
| (7.12) | equation | `eq:F-k-recurrence` | `main.tex:2869` | covered | `psi_insert_max`, `geomSum_succ` |
| 7.4 | example | `ex:B3` | `main.tex:2890` | expository | — |
| 7.5 | theorem | `thm:pretorsion-gandhi` | `main.tex:2919` | covered | `gandhiPretorsion`, `theoremBPretorsion` (`MainTheorems.lean`); `cpSum_eq` (`LinearQuiver/CutoffRestriction.lean`) |
| (7.13) | equation | `eq:pretorsion-D` | `main.tex:2922` | covered | `gandhiPretorsion` |
| (7.14) | equation | `eq:pretorsion-B` | `main.tex:2928` | covered | `theoremBPretorsion` |
| 7.6 | remark | `rem:Catalan-coefficient` | `main.tex:2945` | expository | — |
| (7.15) | equation | `eq:pretorsion-genocchi` | `main.tex:2983` | out of scope (cites the literature for `B_m(1,1) = g_{2m+2}`) | — |
| 8.1 | definition | `def:admissible-starts` | `main.tex:3013` | defined | `admFin`, `adm` (`LinearQuiver/FamilyRestriction.lean`) |
| (8.1) | equation | `eq:admissible-starts` | `main.tex:3017` | covered | `mem_admFin`, `castSucc_mem_adm`, `last_mem_adm` |
| 8.2 | example | `ex:admissible-starts` | `main.tex:3029` | expository | — |
| 8.3 | construction | `con:image-extension` | `main.tex:3053` | covered | `IntervalFamily.glue`, `IntervalFamily.glue_JOf`, `IntervalFamily.JOf_glue` (`LinearQuiver/FamilyRestriction.lean`) |
| (8.2) | equation | `eq:D-J` | `main.tex:3057` | covered | `IntervalFamily.glue`, `mem_glue_castSucc`, `mem_glue_last`, `IntervalFamily.glue_JOf` |
| 8.4 | lemma | `lem:admissible-extension` | `main.tex:3070` | covered: (1) `JOf_subset_adm`, `IntervalFamily.IsClosed.glue`; (2) `admFin_glue`, `card_adm_glue` | `LinearQuiver/FamilyRestriction.lean` |
| (8.3) | equation | `eq:admissible-update-empty` | `main.tex:3077` | covered (the case `J = ∅` of `admFin_glue`) | `admFin_glue` |
| (8.4) | equation | `eq:admissible-update-nonempty` | `main.tex:3081` | covered (as `admFin_glue`, counted by `card_adm_glue`) | `admFin_glue` |
| (8.5) | equation | `eq:admissible-polynomial` | `main.tex:3162` | defined | `fSum` (`LinearQuiver/FamilyRestriction.lean`) |
| (8.6) | equation | `eq:admissible-monomial-transfer` | `main.tex:3191` | covered | `theta_eq` (`Gandhi/ColumnSum.lean`) |
| (8.7) | equation | `eq:admissible-transfer` | `main.tex:3198` | covered | `fSum_succ` |
| (8.8) | equation | `eq:image-from-P` | `main.tex:3220` | covered | `xSum_succ` |
| 8.5 | theorem | `thm:image-gandhi` | `main.tex:3230` | covered | `gandhiImageClosed`, `theoremBImageClosed` (`MainTheorems.lean`); `isGandhiSecond_gandhiSecondOf`, `xSum_eq` |
| (8.9) | equation | `eq:image-C` | `main.tex:3233` | covered | `gandhiImageClosed` |
| (8.10) | equation | `eq:image-C-at-one` | `main.tex:3239` | covered | `theoremBImageClosed` |
| (8.11) | equation | `eq:P-C-induction` | `main.tex:3246` | covered (as `xSum_eq`) | `LinearQuiver/FamilyRestriction.lean` |
| (8.12) | equation | `eq:image-recurrence-substitution` | `main.tex:3272` | covered | `isDelta_X_mul_comp` (`Gandhi/Delta.lean`), `isGandhiSecond_gandhiSecondOf` |
| 8.6 | example | `ex:C3` | `main.tex:3301` | expository | — |
| (8.13) | equation | `eq:image-median` | `main.tex:3323` | out of scope (a numerical consequence quoted from the literature) | — |
| 8.7 | remark | `rem:normalized-image` | `main.tex:3327` | expository | — |
| 8.8 | remark | `rem:orientation-counts` | `main.tex:3341` | expository | — |

## Cited inputs

| Input | Used by | Status | Lean |
|---|---|---|---|
| Campanini–Fedele–Yıldırım, Lemma 2.6, Proposition 2.8 and dual | Proposition 2.3 | covered | `IsPretorsionTheory.isQuotientClosed`, `IsPretorsionTheory.isSubobjectClosed` |
| Facchini–Finocchiaro–Gran, Propositions 2.1–2.2 | Lemma 2.11 | covered | `IsPrekernel.mono`, `IsPrecokernel.epi` |
| Facchini–Finocchiaro–Gran, Proposition 3.9 and dual | Corollary 2.13 | covered | `IsPretorsionTheory.prop_iff_prop_trace`, `IsPretorsionTheory.prop_iff_prop_cokernel_reject` |
| Auslander–Smalø, Proposition 4.8, Corollary 4.9 | Proposition 2.10 | covered | as Proposition 2.10 |
| Auslander–Smalø, Proposition 4.3 | Corollary 4.9 | covered | as Corollary 4.9 |
| Auslander–Smalø, Proposition 4.10(i) | Theorem A (1) ⇔ (2) | covered | `isImageClosed_iff_eq_gen_inf_cogen` |
| Enomoto, *An equidistribution conjecture…*, Proposition 2.13 and Corollary 2.14 (anti-exchange of `qcl`, `scl`) | Theorem 4.11 | covered (adapted from the equidistribution formalization) | `IndecomposableSkeleton.qClosure_isAntiExchange`, `IndecomposableSkeleton.sClosure_isAntiExchange` |
| Auslander–Smalø, Proposition 2.2 | Proposition 4.13(1)–(2) | covered (adapted from the equidistribution formalization) | `not_mem_qClosure_sdiff_iff_isRelativeSplitProjective`, `not_mem_sClosure_diff_iff_relativeSplitInjective` |
| Edelman–Jamison, Theorem 2.1(d)–(e) | Corollary 4.14(2) | covered (finitary form, adapted from the equidistribution formalization) | `SetClosure.compact_extremePoints_basis`, `SetClosure.extremePoints_subset_of_closure_eq` (`ConvexGeometry/`) |
| Thomas, Proposition 6.1 | Proposition 5.2 | covered (proved directly) | as Proposition 5.2 |
| Classification of indecomposable `Λ_n`-modules by intervals | Section 5 onward | covered: every representation is an iterated direct sum of intervals (`intervalSum`), intervals are indecomposable (`indecomposable_interval`), isomorphic intervals coincide (`interval_iso_iff`), indecomposables are intervals (`exists_iso_interval_of_indecomposable`) | `LinearQuiver/Decomposition.lean`, `LinearQuiver/Indecomposables.lean` |
| Krull–Schmidt and finite-length module facts | Lemma 2.9, `ind` of a subcategory | covered: decomposition into indecomposables (`FiniteLengthDecomposition.exists_fin_biproduct_decomposition`), local endomorphism rings (`isLocalRing_end_of_isIndecomposable`), indecomposable retracts of sums (`index_mem_of_retract_inAdd`); the abstract Sections 2–4 use a length function instead | `Modules/IndecomposableModule.lean`, `IndecomposableClosures/` |
