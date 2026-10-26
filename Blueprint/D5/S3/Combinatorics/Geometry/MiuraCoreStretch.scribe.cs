using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreStretchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreStretch.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrarily long actual frozen runs.", H("Arbitrarily long actual frozen runs"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorestretch-0"),
                DeclarationHandle.Create(Prefix + "stretchColumn"), H("Extend one genuine frozen run"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Insert immediately before a frozen column using its actual common signed slope."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorestretch-1"),
                DeclarationHandle.Create(Prefix + "stretchColumn_reduction"), H("The extension reduces back exactly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inserted column and the shifted original column form a genuine consecutive frozen pair. Deleting the inserted column returns the identical original array, giving a legal column-reduction step."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorestretch-2"),
                DeclarationHandle.Create(Prefix + "stretchColumn_residual"), H("Extension preserves the exact split and sides"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine frozen-run extension preserves the normalized residual predicate with the original exact minimum and maximum counts and the original common-side exclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorestretch-3"),
                DeclarationHandle.Create(Prefix + "residual_frozen_run_extension"), H("Every extra run length has an actual realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From an actual residual array with a frozen column, every natural L gives a residual array with L extra columns, a legal deletion chain back to the original array, a remaining frozen column, and preservation of every originally frozen row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorestretch-4"),
                DeclarationHandle.Create(Prefix + "residual_joint_run_extension"), H("Both dimensions vary on the same actual array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If an actual residual array has a frozen line on each axis, then for every pair of natural L,K there is one residual array with L extra rows and K extra columns and a joint signed deletion chain back to the original array. The column extension preserves the row seam needed for the second extension. No uniqueness of expansions or of reduced cores is asserted."))), DescribeRole.Theorem))));
}
