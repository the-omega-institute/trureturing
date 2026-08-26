using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SubmodularCaptureWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named models, premise attacks, and universal refutations guard every capture clause.",
        H("Named Witnesses For Submodular Capture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("submodular-capture-witness-package"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "SubmodularCaptureWitnesses."
                        + "submodular_capture_witnesses_nonvacuous"),
                H("All capture witnesses and premise attacks occur together"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Wquant is finite_capture_laws_nonvacuous. Its three-edge Boolean model "
                            + "consumes the first seven theorem conjuncts and records exact M and "
                            + "F values, a nonempty captured union, strict monotonicity, strict "
                            + "submodularity, strict marginal decrease, and the greedy rewrite.")),
                    Paragraph(Text(
                        "Wblind is fixed_language_blind_pair_persists_witness and consumes the "
                            + "eighth theorem conjunct on a concrete unequal Boolean pair. Wsubset "
                            + "is subset_premise_is_necessary_witness: the candidate is absent "
                            + "from B, but reversing A subset B makes the marginal inequality "
                            + "false. Wzero is constant_zero_weight_is_admissible_witness: its "
                            + "baseline defect is nonempty, costs are nonnegative, and its zero "
                            + "mass is finitely additive but not positive. This guards the removal "
                            + "of the unsupported global positivity premise.")),
                    Paragraph(Text(
                        "Wadditive is finite_additivity_is_necessary_witness, whose proof "
                            + "directly reuses the canonical theorem "
                            + "marginal_capture_law_not_implied_by_escape_weight. Its object is "
                            + "the CAS marginalCaptureLaw over the canonical defectRelation, so "
                            + "it shows the weaker EscapeWeight fields alone do not imply "
                            + "diminishing capture. No second countermodel or residual is defined.")),
                    Paragraph(Text(
                        "WfalseC1 through WfalseC8 are the named theorems "
                            + "clause_one_false_neighbor_witness through "
                            + "clause_eight_false_neighbor_witness. C1 through C7 are universally "
                            + "quantified refutations under exactly the theorem premises, including "
                            + "their finite-selection source-domain conditions. They "
                            + "respectively refute denial of the exact residual-mass formula; "
                            + "denial of F(S)=M(empty)-M(S); denial of the captured-union expansion; "
                            + "strict reverse monotonicity; strict reverse submodularity; strictly "
                            + "increasing marginal capture while retaining subset and freshness; "
                            + "and denial of the residual-score/capture-score equivalence. Thus "
                            + "their negations are theorems for every admissible model, not facts "
                            + "that happen only in one finite model. C8 is likewise universal but "
                            + "has no finite-selection premise: it flips only the conclusion from "
                            + "membership to nonmembership and refutes that neighbor under the "
                            + "unchanged blind-pair hypotheses.")),
                    Paragraph(Text(
                        "The displayed present labels are deliberately weaker than the Lean "
                            + "conjunction. The Lean consumer repeats and consumes the complete "
                            + "statement of every witness, including all strict inequalities, "
                            + "memberships, equalities, premise failures, and the existential "
                            + "weak-weight countermodel.")),
                    Paragraph(Text(
                        "scribe_lean_correspondence: Wquant maps to "
                            + "finite_capture_laws_nonvacuous; Wblind to "
                            + "fixed_language_blind_pair_persists_witness; Wsubset to "
                            + "subset_premise_is_necessary_witness; Wzero to "
                            + "constant_zero_weight_is_admissible_witness; and Wadditive to "
                            + "finite_additivity_is_necessary_witness. WfalseC1 through WfalseC8 "
                            + "map in order to clause_one_false_neighbor_witness through "
                            + "clause_eight_false_neighbor_witness. Each of these thirteen Formula "
                            + "items is weaker because present(name) omits the full Lean statement. "
                            + "Equal mappings: zero. Stronger mappings: zero."))),
                DescribeRole.Theorem))));

    private static Formula WitnessFormula() => Disp(Seq(
        Present(F.Id("Wquant")), Sp, Land, Sp,
        Present(F.Id("Wblind")), Sp, Land, Sp,
        Present(F.Id("Wsubset")), Sp, Land, Sp,
        Present(F.Id("Wzero")), Sp, Land, Sp,
        Present(F.Id("Wadditive")), Sp, Land, Sp,
        Present(F.Id("WfalseC1")), Sp, Land, Sp,
        Present(F.Id("WfalseC2")), Sp, Land, Sp,
        Present(F.Id("WfalseC3")), Sp, Land, Sp,
        Present(F.Id("WfalseC4")), Sp, Land, Sp,
        Present(F.Id("WfalseC5")), Sp, Land, Sp,
        Present(F.Id("WfalseC6")), Sp, Land, Sp,
        Present(F.Id("WfalseC7")), Sp, Land, Sp,
        Present(F.Id("WfalseC8"))));

    private static Formula Present(Formula witness) => Call("present", witness);
}
