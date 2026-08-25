using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class DirectlyProvableLawWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten named witnesses make every packaged direct DECT law mechanically nonvacuous.",
        H("Named Nonvacuity Witnesses For The Direct DECT Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("direct-decl-laws-witness-package"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "DirectlyProvableLawWitnesses."
                        + "directly_provable_laws_witnesses_nonvacuous"),
                H("All named direct-law witnesses are present together"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed present labels are a deliberately weaker summary of the "
                            + "Lean conjunction. In source order, the Lean theorem extracts a "
                            + "concrete residual pair for clause one, identity factorization for "
                            + "clause two, both a redundant-readout pair and the Empty-state "
                            + "FactorsThrough-not-Refines separation for clause three, a blind "
                            + "pair for clause four, finite closure from a nonempty baseline "
                            + "defect for clause five, nonzero prepared and semigroup defects for "
                            + "clauses seven and eight, and a tight cascade bound for clause nine.")),
                    Paragraph(Text(
                        "Each of those eight source-law positions consumes the matching projection "
                            + "of directly_provable_laws. The final present label is an adjacent "
                            + "strict captured-mass submodularity example. It is consumed by the "
                            + "package but is not source clause six and does not close TASK "
                            + "D5-T0049.")),
                    Paragraph(Text(
                        "W1, W2, W3a, W3b, W4, W5, W7, W8, W9, and Wcapture map "
                            + "respectively to clause1_nonvacuity_witness, "
                            + "clause2_nonvacuity_witness, clause3_nonvacuity_witness, "
                            + "clause3_fiber_constancy_not_refines_witness, "
                            + "clause4_nonvacuity_witness, clause5_nonvacuity_witness, "
                            + "clause7_nonvacuity_witness, clause8_nonvacuity_witness, "
                            + "clause9_nonvacuity_witness, and "
                            + "adjacent_capture_submodularity_strict_witness.")),
                    Paragraph(Text(
                        "There are ten names because clause three has two independent checks and "
                            + "the adjacent capture boundary is retained separately. The package "
                            + "references every name, so deleting any witness makes the package "
                            + "fail to elaborate instead of silently removing an anonymous "
                            + "example."))),
                DescribeRole.Theorem))));

    private static Formula WitnessFormula() => Disp(Seq(
        Present("W1"), Sp, Land, Sp,
        Present("W2"), Sp, Land, Sp,
        Present("W3a"), Sp, Land, Sp,
        Present("W3b"), Sp, Land, Sp,
        Present("W4"), Sp, Land, Sp,
        Present("W5"), Sp, Land, Sp,
        Present("W7"), Sp, Land, Sp,
        Present("W8"), Sp, Land, Sp,
        Present("W9"), Sp, Land, Sp,
        Present("Wcapture")));

    private static Formula Present(string declaration) =>
        Call("present", F.Id(declaration));
}
