# RewThree declaration evidence

This table joins source commands to the kernel report by full Lean name. The previous empty table compared unqualified source names with `LO.FirstOrder...` names; it was an evidence-generation failure, not a zero-declaration result.

Input HEAD: `61900643d4451a784e4e1801baeca5c38d06b6ba`.
Raw Lean report SHA-256: `sha256:3872f6538b16ed92226d98c1199c46cb2d91aa5104b0bb95467a034292eb287b`.

The enclosing Git commit binds this artifact. [declaration-audit.json](declaration-audit.json) records every public report declaration, its statement identity, all captured direct frozen dependencies (module GID and module/declaration statement IDs), internal edges, axioms, source mapping, assessment and limitations. These are evidence records, not new mathematics or a complete CSA.

For every authored theorem below, `proof_shape=bind-only`, `escape_witness=none`, and `admission_basis=rule-11-upstream-wrapper`. Definitions, classes and macros use their stated shape and the same upstream basis. The exact upstream is [Foundation Rew.lean at 30a16ffa](https://github.com/FormalizedFormalLogic/Foundation/blob/30a16ffa93d79d73ab4d02427fa00f50e039bf29/Foundation/Syntax/Predicate/Rew.lean).

| Public source declaration | Kind / proof_shape | Local lines | Exact upstream lines | Direct frozen dependency records |
| --- | --- | --- | --- | --- |
| `LO.FirstOrder.substNotation` | def / macro | RewThree:187-193 | 872-878 | 0; exact GID + statement IDs in JSON |
| `LO.FirstOrder.InjMapRewriting` | inductive / class | RewThree:207-210 | 897-900 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.SyntacticRewriting` | def / definition | RewThree:143-144 | 814-815 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.ReflectiveRewriting` | inductive / class | RewThree:197-199 | 887-889 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.TransitiveRewriting` | inductive / class | RewThree:201-205 | 891-895 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.LawfulSyntacticRewriting` | inductive / class | RewThree:212-213 | 902-903 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.«term_⁺»` | def / macro | RewThree:169-170 | 854-855 | 0; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting` | inductive / class | RewThree:137-141 | 808-812 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.LawfulSyntacticRewriting.shift_conj₂` | theorem / bind-only | RewThree:223-229 | 930-936 | 16; exact GID + statement IDs in JSON |
| `LO.FirstOrder.LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free` | theorem / bind-only | RewThree:234-235 | 951-953 | 14; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rew.fixitr_bvar` | theorem / bind-only | RewThree:32-36 | 639-643 | 14; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rew.fixitr_fvar` | theorem / bind-only | RewThree:38-52 | 645-659 | 16; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.emb_toEmpty` | theorem / bind-only | RewThree:122-124 | 786-788 | 13; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.lMap_bShift` | theorem / bind-only | RewThree:87-88 | 740-741 | 8; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.fvar?_bShift` | theorem / bind-only | RewThree:108-110 | 772-774 | 15; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.rew_eq_of_funEqOn` | theorem / bind-only | RewThree:62-72 | 715-725 | 15; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.toEmpty` | def / definition | RewThree:112-120 | 776-784 | 5; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.lMap_map` | theorem / bind-only | RewThree:83-85 | 736-738 | 10; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.fvar?_rew` | theorem / bind-only | RewThree:92-106 | 756-770 | 12; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.lMap_bind` | theorem / bind-only | RewThree:79-81 | 732-734 | 12; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.shifts_neg` | theorem / bind-only | RewThree:176-177 | 861-862 | 12; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.shifts_nil` | theorem / bind-only | RewThree:172 | 857 | 2; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.shifts_cons` | theorem / bind-only | RewThree:174 | 859 | 6; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.emb` | def / definition | RewThree:179 | 864 | 6; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.free` | def / definition | RewThree:165 | 848 | 6; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.shift` | def / definition | RewThree:162-163 | 845-846 | 6; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.subst` | def / definition | RewThree:157 | 840 | 8; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.shifts` | def / definition | RewThree:167 | 852 | 6; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.smul_ext'` | theorem / bind-only | RewThree:155 | 826 | 7; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.«term_⇜_»` | def / macro | RewThree:159-160 | 842-843 | 0; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Rewriting.«term_▹_»` | def / macro | RewThree:152-153 | 823-824 | 0; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.shifts_neg` | theorem / bind-only | RewThreeCompat:66-68 | 861-862 | 10; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.shifts_nil` | theorem / bind-only | RewThreeCompat:58-60 | 857 | 5; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.shifts_cons` | theorem / bind-only | RewThreeCompat:62-64 | 859 | 10; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.substNotation` | def / macro | RewThreeCompat:76-79 | 872-878 | 0; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.shift_conj_two` | theorem / bind-only | RewThreeCompat:47-48 | 930-936 | 13; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free` | theorem / bind-only | RewThreeCompat:52-54 | 951-953 | 14; exact GID + statement IDs in JSON |
| `LO.FirstOrder.RewThreeCompat.emb` | def / definition | RewThreeCompat:70-72 | 864 | 7; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.fvar_bShift` | theorem / bind-only | RewThreeCompat:34-36 | 772-774 | 7; exact GID + statement IDs in JSON |
| `LO.FirstOrder.Semiterm.fvar_rew` | theorem / bind-only | RewThreeCompat:27-32 | 756-770 | 8; exact GID + statement IDs in JSON |

Authored source-command rows: **40**. Public kernel-report records: **94**. Generated records have no independent source declaration or novelty claim; their JSON entries record the parent source-command range when identified by a declaration prefix, and explicitly identify missing nonauxiliary dependency capture rather than reporting an empty dependency set as verified.

The machine data do not determine proof shape. The bind-only assessment follows the retained-upstream/forwarding basis recorded in `Library/ConceptDynamics/foundation2026firstorder.md`; it does not reclassify upstream induction proofs as newly authored content.
