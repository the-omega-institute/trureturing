using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalReindexedLawsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual proper-slice laws after whole-birth reindexing", H("Reindexed actual signed laws"), Blocks(
            Describe.Lean(DescribeId.Create("reindexed-laws-old-index"),
                DeclarationHandle.Create(Owner + "oldIndex"), H("The original decoded measure label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At each row from omega onward, decode with measureIndex of the actual wholeBirth in SignedOrdinalRealization.finalPrefix under CH. Finite rows retain their original labels. The decoded label is at most the new label."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reindexed-laws-old-coordinate"),
                DeclarationHandle.Create(Owner + "oldCoord"), H("The decoded coordinate in the same proper slice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a label in the proper slice, its decoded label remains in that exact slice because it is at most the given label. No additional strict bound on the birth row or later carrier is required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reindexed-laws-proper-data"),
                DeclarationHandle.Create(Owner + "properData"), H("Concrete reindexed proper Data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every cutoff below omega-one, use the original actual properSlice and properData. I, V and the clopen certificate remain literal originals. Nu reads the original whole sequence at the decoded measure label; J and N read the original tables at that decoded coordinate. Properness and mass are inherited. Zero, finite, omega and successor cutoffs, including successor last rows, are covered."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reindexed-laws-proper-laws"),
                DeclarationHandle.Create(Owner + "properLaws"), H("All original signed A through F laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The decoded coordinate is at most the new coordinate, so every eligible new label is eligible for the original A, C, DJ and F. B uses the same decoded reservoirs; DI and E use the identical I and V. The new OldClass equals the original OldClass at the decoded coordinate. Thus original F applies to every arbitrary all-natural sequence of regular signed norm-preserving lifts, retaining the same regular reference with norm at most one and the same weak convergence filter. No positivity or selected-sequence replacement is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reindexed-laws-nu-read"),
                DeclarationHandle.Create(Owner + "nu_read"), H("Every natural entry is the original whole-birth measure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every born row, every label below omega-one and every natural index, slice_nu identifies the new signed measure with the actual wholeBirth measure at measureIndex. The label need not be below the slice cutoff, and newborn last rows need no later carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reindexed-laws-nu-reindex-birth"),
                DeclarationHandle.Create(Owner + "nu_reindexBirth"), H("Compatibility with generic whole-birth reindexing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any delayed support on the same actual carrier, the concrete proper Data nu agrees at every label and natural index with reindexBirth of that same wholeBirth. Its nu is independent of delayedSupport."))), DescribeRole.Theorem),
            Paragraph(Text("The proper-stage adapter uses the same actual finalPrefix and whole-birth measures as SignedOrdinalActualReindex and SignedOrdinalActualG. Its full signed F laws and all-natural-index measure readback can therefore be used with that fixed global eta, universal support launch and successor G.")))));
}
