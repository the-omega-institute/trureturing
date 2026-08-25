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
                        "The Lean package consumes the complete statement of every named witness, "
                            + "including all premises, equalities, memberships, nonemptiness claims, "
                            + "factorizations, obstructions, and strict or tight inequalities. The "
                            + "displayed present labels only record the weaker fact that all ten "
                            + "complete witnesses occur together. The final label is an adjacent "
                            + "strict captured-mass submodularity example; it is not source clause "
                            + "six and does not close TASK D5-T0049.")),
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
                            + "requires each full witness type, so deleting any witness or weakening "
                            + "any conjunct in one makes the package fail to elaborate instead of "
                            + "silently accepting a decorative example."))),
                DescribeRole.Theorem))));

    private static Formula WitnessFormula() => Disp(Seq(
        Present(F.Id("W1")), Sp, Land, Sp,
        Present(F.Id("W2")), Sp, Land, Sp,
        Present(F.Id("W3a")), Sp, Land, Sp,
        Present(F.Id("W3b")), Sp, Land, Sp,
        Present(F.Id("W4")), Sp, Land, Sp,
        Present(F.Id("W5")), Sp, Land, Sp,
        Present(F.Id("W7")), Sp, Land, Sp,
        Present(F.Id("W8")), Sp, Land, Sp,
        Present(F.Id("W9")), Sp, Land, Sp,
        Present(F.Id("Wcapture"))));

    private static Formula Present(Formula declaration) =>
        Call("present", declaration);
}
