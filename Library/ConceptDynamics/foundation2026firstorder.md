---
bibkey: foundation2026firstorder
authors: FormalizedFormalLogic contributors
year: 2026
title: Foundation first-order logic and set theory, revision 30a16ffa
doi: null
url: https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29
claim: Licensed logic, predicate-term and finite formula syntax, entailment, finite support, language maps, empty-domain elimination and unique choice for first-order developments.
strata_touched:
  - D5/S3/ConceptDynamics/ZfcEntailment/CalculusOne
  - D5/S3/ConceptDynamics/ZfcEntailment/CalculusTwo
  - D5/S3/ConceptDynamics/ZfcEntailment/EntailmentOne
  - D5/S3/ConceptDynamics/ZfcEntailment/EntailmentTwo
  - D5/S3/ConceptDynamics/ZfcFiniteCollections/Finset
  - D5/S3/ConceptDynamics/ZfcFiniteCollections/List
  - D5/S3/ConceptDynamics/ZfcFiniteCollections/Matrix
  - D5/S3/ConceptDynamics/ZfcFiniteCollections/Quotient
  - D5/S3/ConceptDynamics/ZfcFiniteData/Fin
  - D5/S3/ConceptDynamics/ZfcFiniteData/Nat
  - D5/S3/ConceptDynamics/ZfcFiniteData/NatMatrix
  - D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty
  - D5/S3/ConceptDynamics/ZfcLanguageSupport/NotationClass
  - D5/S3/ConceptDynamics/ZfcLogic/ForcingRelation
  - D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolOne
  - D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolTwo
  - D5/S3/ConceptDynamics/ZfcLogic/Semantics
  - D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentFour
  - D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentOne
  - D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentThree
  - D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentTwo
  - D5/S3/ConceptDynamics/ZfcPredicate/LanguageOne
  - D5/S3/ConceptDynamics/ZfcPredicate/LanguageTwo
  - D5/S3/ConceptDynamics/ZfcPredicate/Quantifier
  - D5/S3/ConceptDynamics/ZfcPredicate/Term
  - D5/S3/ConceptDynamics/ZfcPropositional/ClEntailment
  - D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentOne
  - D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentTwo
  - D5/S3/ConceptDynamics/ZfcSupport/AdjunctiveSet
  - D5/S3/ConceptDynamics/ZfcSupport/Function
  - D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice
  - D5/S3/ConceptDynamics/ZfcSyntax/FormulaOne
  - D5/S3/ConceptDynamics/ZfcSyntax/FormulaTwo
  - D5/S3/ConceptDynamics/ZfcTermRewriting/RewOne
  - D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo
  - D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour
license: Apache-2.0
triage: anchor
---
<!-- GID: D5/L/ConceptDynamics/foundation2026firstorder -->
# foundation2026firstorder

## Verified locator

Immutable source: [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29),
revision `30a16ffa93d79d73ab4d02427fa00f50e039bf29`. The table below locates the
selected sources within this immutable revision; its SHA-256 digests identify the
complete original upstream files.
Copyright and attribution remain with the upstream contributors. Original author notices and
required source notices are preserved. The upstream distribution has no NOTICE file.
The complete unmodified Apache-2.0 license follows below.

The installed layer contains 36 modules from 25 immutable upstream source files,
with 4,592 Lean source lines (including headers and blank lines). Its source footprint
is 36 Lean files, 36 Scribe sources and 36 Markdown twins, plus this shared note:
109 files. The table lists exactly the installed Lean paths; each `strata_touched`
GID resolves to its corresponding Lean/Scribe/Markdown triple.

Each row preserves the original source path, SHA-256 and capacity span. Only selected
command excerpts within those spans are copied; neither whole-file nor whole-span
verbatim copying is asserted. Resolve each original path relative to the immutable
upstream revision linked above. This is a source transplant, with no installed
upstream package dependency or package-pin change.

The layer supplies logic symbols, semantic and forcing-relation interfaces, entailment
and propositional calculi, predicate-language and term syntax, rewriting support and
finite-data utilities for first-order developments. FormulaOne supplies the actual
finite inductive first-order formula carrier with arbitrary relation arities, separate
free variables and finite bound-variable indices, connectives, quantifiers, negation,
structural recursion, complexity and conditional decidable equality. FormulaTwo adds
finite free-variable support, bounds for natural-number variables and language maps
with connective and quantifier preservation. This formula construction/support pair
depends only on the frozen D5 Term/Quantifier APIs and pinned Mathlib; FormulaTwo also
imports FormulaOne. These general APIs have independent mathematical use before the
later term/formula rewriting and CSA graph-elimination layers.

References in the Scribe prose to a concrete pair interpretation describe intended
downstream use. This layer does not
install a pair-language or pair-interpretation interface, establish ZFC conservativity
or a relative-consistency bridge, construct the full CSA, or prove ZFC model existence
or absolute consistency. Internal HF/omega, finite archives, CSA arithmetic and
rational/Cauchy-sequence constructions, and the complete CSA defining-graph and
elimination obligations are outside this layer's scope. It does not identify an
internal nonstandard carrier with a Lean type or establish source-atom coverage.

The Empty/UniqueChoice support pair supplies equality of every map from an empty
domain with its eliminator, and the chosen witness and specification of a proved
unique existence on an arbitrary sort. It assumes no model of ZFC and does not
establish full definitional conservativity. These are general API utilities
(`utility: none`), with individually necessary rule-11 upstream-wrapper candidates
and one compiler-generated exact-command companion. Generation supplies no new
escape, proof-value, liveness or indispensability credit. The two Lean theorem
names `Classical.choose!_spec` and `Classical.choose!_eq_iff_right` remain in prose
with their typed formulas; `choose_uniq` is the legal direct selector. This pair has
independent support meaning before the separate countable-filter and CSA
interpretation layers. OrderDense remains preserved outside this installed layer.

Modifications are canonical headers, import reduction/relocation, source-command excerpts,
capacity scope boundaries and restricting attribute target lists to needed relation
projections. The retained mathematical command bodies remain upstream bytes.

The Semantics selection omits precisely the optional `Semantics.Top (Set M)`
instance command at `Foundation/Logic/Semantics.lean:251` (the upstream authored
instance named `LO.Semantics.instTopSet` by Lean). The selected
`set_models_iff`, `set_meaningful_iff_nonempty` and
`meaningful_iff_satisfiableSet` commands retain their original proofs. In
particular, the original `simpa [NotModels, set_models_iff]` remains in the
nonemptiness proof. Compiler normalization helpers are generated from the retained
proof source; their ownership does not establish a need for the omitted instance.
The capacity span below locates the excerpts and includes this explicit exclusion.

The FormulaOne selection omits the optional upstream theorem
`LO.FirstOrder.Semiformula.neg_allClosure`. The retained formula carrier and support
commands preserve their original mathematical bodies and hypotheses; this exclusion
belongs to the selected excerpts within FormulaOne's capacity span below.

RewTwo supplies variable-domain lifts, binder shifts, `shift`, `free`, `fix`,
their bound/free-variable laws, composition and substitution identities, q-lifts
and finite `fixitr` iteration on actual first-order terms. It retains the supplied
source commands and hypotheses except the optional `LO.FirstOrder.Rew.q_emb`.
The supplied selection input is SHA-256
`6639a4bd42da9b1cd99728d18f301d367f0a75c3afd0728373ce35c8ef55335c` (6,268 bytes);
the installed source, after that omission, is SHA-256
`b68465527cc3e61f7f31322848f3421d60b533f8195861822bb7ed2b98a91652`. These source digests are distinct from
the complete upstream-file digest in the table. Historical 49-occurrence evidence
associated with source SHA-256
`d46397c4c5fb43b10a44c0596f5d7ab181e5e11a42ccd326611abe066825b2e8`
is historical association evidence only; current identities require the current
source-bound canonical report. Its 33 rule-11 upstream-wrapper proposals and 16
generated-source/API associations confer no new escape, liveness or
indispensability credit. Theorems remain bind-only; definitions and other
non-theorems have null proof shape. These general APIs do not prove the CSA
set-coding, defining-graph elimination or ZFC conservativity bridge.

RewFour supplies the retained lawful syntactic-rewriting identities for free-variable
rewriting and shifts, bound-slot lifting, substitution and casting. Its
selected source commands occupy `Foundation/Syntax/Predicate/Rew.lean:954-1080`
at the pinned revision; the seven public declarations are theorem observations with
bind-only proof shape, while generated simplifier companions are compiler output.
This excerpt preserves the upstream hypotheses and proof bodies and adds no pair
interpretation or definition-elimination theorem.

The installed RewFour source is SHA-256
`dc8b4a511119829e95a2bcf9c4f3db17e102fcbe8df882d12b1933dc25bebeda`.
Each declaration below retains the corresponding command bytes in the same upstream
namespace `LO.FirstOrder.LawfulSyntacticRewriting`; the spans refer to the immutable
revision above. Its direct D5 imports are `ZfcPredicate/Quantifier`,
`ZfcPredicate/Term`, `ZfcSupport/Function` and `ZfcTermRewriting/RewThree`, all under
`D5/S3/ConceptDynamics`. The remaining direct import is toolchain `Init`.

| RewFour declaration | Original command lines | General API identity |
| --- | --- | --- |
| `free_rewrite_eq` | 955–958 | Freeing a bound slot transports a lifted replacement map. |
| `shift_rewrite_eq` | 960–962 | Free-variable shifting transports the replacement map. |
| `rewrite_subst_eq` | 964–966 | Rewriting a substitution rewrites both the formula and substituted term. |
| `free_subst_nil` | 968–970 | Freeing an unused bound slot equals free-variable shifting. |
| `rewrite_subst_nil` | 972–978 | A lifted rewrite commutes with adding an unused bound slot. |
| `cast_subst_eq` | 980–985 | Substitution into an unused bound slot recovers the formula. |
| `rewrite_free_eq_subst` | 987–989 | Freeing followed by the specified rewrite equals substitution. |

Retirement: replace a transplanted API by a direct Mathlib reference when the repository's pin
provides a proved-equivalent syntax/theory/proof/definability API and its faithful bridge
elaborates. Upstream PR acceptance alone is insufficient.

| Installed D5 source path | Original source | Original capacity span (excerpts only) | Original SHA-256 |
| --- | --- | --- | --- |
| D5/S3/ConceptDynamics/ZfcFiniteData/Nat.lean | Foundation/Vorspiel/Nat/Basic.lean | 1–63 | 0a138628fbf374d982138b0d731c741a980db093cde30ca21e6a5c697a5d5972 |
| D5/S3/ConceptDynamics/ZfcFiniteData/Fin.lean | Foundation/Vorspiel/Fin/Basic.lean | 1–109 | a87e63e094316c344a59e6764d457d715f752a1a5098eb407a15f5dbbb14cdf4 |
| D5/S3/ConceptDynamics/ZfcFiniteCollections/Matrix.lean | Foundation/Vorspiel/Matrix.lean | 1–341 | e7f8dd76125d5e7ae5017ed1f837819fff4c95bdb704af956ec71b428d94bf93 |
| D5/S3/ConceptDynamics/ZfcFiniteCollections/List.lean | Foundation/Vorspiel/List/Basic.lean | 1–300 | 7f8fd76c712399fd0cc2c161c4700e3b70158e44561141b220a8273db3e75c2e |
| D5/S3/ConceptDynamics/ZfcLanguageSupport/NotationClass.lean | Foundation/Vorspiel/NotationClass.lean | 1–136 | 82d86dc4dd83f435526f429c28e5a4e42b189f4009d4eeddc1b0c58d4bffc155 |
| D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolOne.lean | Foundation/Logic/LogicSymbol.lean | 1–319 | 1f2c86c28a9af8428bd9f456e5e05110a1ce7e36844980063c9b8cc157125bee |
| D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolTwo.lean | Foundation/Logic/LogicSymbol.lean | 320–638 | 1f2c86c28a9af8428bd9f456e5e05110a1ce7e36844980063c9b8cc157125bee |
| D5/S3/ConceptDynamics/ZfcLogic/Semantics.lean | Foundation/Logic/Semantics.lean | 1–363; selected commands exclude line 251 | 759358f8de447fae0d1ba0f19c4814e5f24ace3181f54550a809f73456623c89 |
| D5/S3/ConceptDynamics/ZfcSupport/AdjunctiveSet.lean | Foundation/Vorspiel/AdjunctiveSet.lean | 1–119 | 53665c5b167237a7ae4f1c2fdbe54b6ff39201bfac47ac73a2c1d7e5ff9414ae |
| D5/S3/ConceptDynamics/ZfcEntailment/EntailmentOne.lean | Foundation/Logic/Entailment.lean | 1–320 | 4c59093a4e631b37669e4cc936f930697ccbb3daacde6dbbeaffc40dcd104aae |
| D5/S3/ConceptDynamics/ZfcEntailment/EntailmentTwo.lean | Foundation/Logic/Entailment.lean | 321–645 | 4c59093a4e631b37669e4cc936f930697ccbb3daacde6dbbeaffc40dcd104aae |
| D5/S3/ConceptDynamics/ZfcPredicate/LanguageOne.lean | Foundation/Syntax/Predicate/Language.lean | 1–318 | b5ef82f9c7198f984d2bfc2a765d67e2f815a6d7d65c1b66eebb3373789b676e |
| D5/S3/ConceptDynamics/ZfcPredicate/LanguageTwo.lean | Foundation/Syntax/Predicate/Language.lean | 319–445 | b5ef82f9c7198f984d2bfc2a765d67e2f815a6d7d65c1b66eebb3373789b676e |
| D5/S3/ConceptDynamics/ZfcPredicate/Term.lean | Foundation/Syntax/Predicate/Term.lean | 1–253 | 6209c01b7b2629cf29b7a226e7421e98c4e1188c4949f0876f237a0ba89c1cfd |
| D5/S3/ConceptDynamics/ZfcPredicate/Quantifier.lean | Foundation/Syntax/Predicate/Quantifier.lean | 1–296 | 9675a51b9bd78a72caa29730242f628b0ace98e9c4b2d0ddfc38636279e1acdc |
| D5/S3/ConceptDynamics/ZfcFiniteCollections/Finset.lean | Foundation/Vorspiel/Finset/Basic.lean | 1–88 | 34c9b64196d84407927c2d8c9332cd07c91cfca871b243acf1bed717c8a27746 |
| D5/S3/ConceptDynamics/ZfcSupport/Function.lean | Foundation/Vorspiel/Function.lean | 1–18 | b6eb4a72d46ac6f11b3ff3951b95f4cfe1b03498f290ad46b9bd75cc626ef796 |
| D5/S3/ConceptDynamics/ZfcTermRewriting/RewOne.lean | Foundation/Syntax/Predicate/Rew.lean | 1–320 | 8df8681a12ebf5ef8700d9710c88fc39bfc35df47ef387e2893df3caf3b69873 |
| D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo.lean | Foundation/Syntax/Predicate/Rew.lean | 321–637; selected commands exclude `LO.FirstOrder.Rew.q_emb` | 8df8681a12ebf5ef8700d9710c88fc39bfc35df47ef387e2893df3caf3b69873 |
| D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.lean | Foundation/Syntax/Predicate/Rew.lean | 954–1080 (selected commands) | 8df8681a12ebf5ef8700d9710c88fc39bfc35df47ef387e2893df3caf3b69873 |
| D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentOne.lean | Foundation/Propositional/Entailment/Minimal.lean | 1–320 | aa8c65b4a9a1c4cb1b5148ea65d159302b11dbcc839bba1184e422413808b8f1 |
| D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentTwo.lean | Foundation/Propositional/Entailment/Minimal.lean | 321–639 | aa8c65b4a9a1c4cb1b5148ea65d159302b11dbcc839bba1184e422413808b8f1 |
| D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentThree.lean | Foundation/Propositional/Entailment/Minimal.lean | 640–959 | aa8c65b4a9a1c4cb1b5148ea65d159302b11dbcc839bba1184e422413808b8f1 |
| D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentFour.lean | Foundation/Propositional/Entailment/Minimal.lean | 960–1272 | aa8c65b4a9a1c4cb1b5148ea65d159302b11dbcc839bba1184e422413808b8f1 |
| D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentOne.lean | Foundation/Propositional/Entailment/Int.lean | 1–309 | fdb99522d112d69b3bcd40f4c0004f2656b2186108a854b59970e1b008ec2361 |
| D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentTwo.lean | Foundation/Propositional/Entailment/Int.lean | 310–463 | fdb99522d112d69b3bcd40f4c0004f2656b2186108a854b59970e1b008ec2361 |
| D5/S3/ConceptDynamics/ZfcPropositional/ClEntailment.lean | Foundation/Propositional/Entailment/Cl.lean | 1–350 | 437ad56a9fa221c6bed9a6472ac5da49d048e5bf00dbd309b5c0386a99f9e78a |
| D5/S3/ConceptDynamics/ZfcEntailment/CalculusOne.lean | Foundation/Logic/Calculus.lean | 1–320 | b92ec1115fe069f7b5b14af1d5b7d0ff53c50aa5efc3d560ab6d81b216e17cdb |
| D5/S3/ConceptDynamics/ZfcEntailment/CalculusTwo.lean | Foundation/Logic/Calculus.lean | 321–376 | b92ec1115fe069f7b5b14af1d5b7d0ff53c50aa5efc3d560ab6d81b216e17cdb |
| D5/S3/ConceptDynamics/ZfcFiniteData/NatMatrix.lean | Foundation/Vorspiel/Nat/Matrix.lean | 1–86 | 1a1cc8e8d58a586247f408c20d31a4acc0ee7a84d6ab45998c082adf95a382ce |
| D5/S3/ConceptDynamics/ZfcFiniteCollections/Quotient.lean | Foundation/Vorspiel/Quotient.lean | 1–44 | d0ee23b967dffb1fce05e4e6eeab82dcf3c583361dba0a31f8c85a12c6b34ef5 |
| D5/S3/ConceptDynamics/ZfcLogic/ForcingRelation.lean | Foundation/Logic/ForcingRelation.lean | 1–155 | 1ccea85946aa4604136ec39cbd413ed475d315a4cd5eca5aaae9b63095ca035c |
| D5/S3/ConceptDynamics/ZfcSyntax/FormulaOne.lean | Foundation/FirstOrder/Basic/Syntax/Formula.lean | 1–320 | 6726460b455fa93f42cd9c1849cf25bf7013cd4d349e7afada5e3678f05162c3 |
| D5/S3/ConceptDynamics/ZfcSyntax/FormulaTwo.lean | Foundation/FirstOrder/Basic/Syntax/Formula.lean | 321–587 | 6726460b455fa93f42cd9c1849cf25bf7013cd4d349e7afada5e3678f05162c3 |
| D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty.lean | Foundation/Vorspiel/Empty.lean | 9 (retained mathematical commands) | f3b5429d4ec0c230a633b343a6ac8cdd079d56c1eaa5812994c95dfd487ab985 |
| D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice.lean | Foundation/Vorspiel/ExistsUnique.lean | 11–18 (retained mathematical commands) | 9326800a0ed419feaa0dd7ebfe63de62371d728b0c4ee5b84b3f093d7e7f871e |

## Apache-2.0 license

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```
