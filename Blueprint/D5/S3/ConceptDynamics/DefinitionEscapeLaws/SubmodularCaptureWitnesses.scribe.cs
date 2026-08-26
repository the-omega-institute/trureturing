using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SubmodularCaptureWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named finite models and attacks mechanically guard every submodular-capture clause.",
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
                            + "false. Wzero is constant_zero_weight_is_rejected_witness: its "
                            + "baseline defect is nonempty and its zero mass is finitely additive, "
                            + "but it fails the strict-positive premise.")),
                    Paragraph(Text(
                        "Wadditive is finite_additivity_is_necessary_witness, whose proof "
                            + "directly reuses the canonical theorem "
                            + "marginal_capture_law_not_implied_by_escape_weight. Its object is "
                            + "the CAS marginalCaptureLaw over the canonical defectRelation, so "
                            + "it shows the weaker EscapeWeight fields alone do not imply "
                            + "diminishing capture. No second countermodel or residual is defined.")),
                    Paragraph(Text(
                        "The five displayed present labels are deliberately weaker than the Lean "
                            + "conjunction. The Lean consumer repeats and consumes the complete "
                            + "statement of every witness, including all strict inequalities, "
                            + "memberships, equalities, premise failures, and the existential "
                            + "weak-weight countermodel."))),
                DescribeRole.Theorem))));

    private static Formula WitnessFormula() => Disp(Seq(
        Present(F.Id("Wquant")), Sp, Land, Sp,
        Present(F.Id("Wblind")), Sp, Land, Sp,
        Present(F.Id("Wsubset")), Sp, Land, Sp,
        Present(F.Id("Wzero")), Sp, Land, Sp,
        Present(F.Id("Wadditive"))));

    private static Formula Present(Formula witness) => Call("present", witness);
}
