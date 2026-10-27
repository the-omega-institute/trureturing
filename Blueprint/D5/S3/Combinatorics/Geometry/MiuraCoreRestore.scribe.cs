using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreRestoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreRestore.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit inverse signed insertion.", H("Explicit inverse signed insertion"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorerestore-0"),
                DeclarationHandle.Create(Prefix + "restoreColumn"), H("Insert the translated preceding profile"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an internal column coordinate j, retain earlier columns and translate the profile at column x-1 by the signed step s for each x at or after j. The inserted column uses the preceding profile."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorerestore-1"),
                DeclarationHandle.Create(Prefix + "restoreColumn_isHeight"), H("Every unit edge survives insertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the original function has unit absolute differences on grid edges and s is either 1 or -1, every vertical and horizontal edge of the inserted array again has unit absolute difference. The new seam contributes exactly s."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorerestore-2"),
                DeclarationHandle.Create(Prefix + "SeamSlope"), H("The actual signed seam condition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every row, the difference between the original columns j and j-1 equals the same integer s. This condition is local to the actual insertion seam."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorerestore-3"),
                DeclarationHandle.Create(Prefix + "restoreColumn_frozen"), H("The inserted column is frozen"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common signed seam equation makes the inserted profile the midpoint of its two neighbouring profiles, so the inserted column satisfies the genuine frozen equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorerestore-4"),
                DeclarationHandle.Create(Prefix + "contractAt_restoreColumn"), H("Contraction inverts insertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonempty row axis and an internal insertion coordinate satisfying the signed seam condition, contracting the inserted frozen column recovers the identical original function."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorerestore-5"),
                DeclarationHandle.Create(Prefix + "restoreColumn_contractAt"), H("Insertion inverts contraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given an actual unit-edge function and one of its genuinely frozen columns, insert its actual common signed slope into the contracted function. Every original cell value, including the deleted column, is recovered exactly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorerestore-6"),
                DeclarationHandle.Create(Prefix + "restoreColumn_residual"), H("The exact residual predicate survives insertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive or negative unit seam insertion into a normalized residual array preserves each minimum and maximum count separately and preserves the failure of all minima to lie on a single common physical side. The seam condition and the unit-edge law are verified on that same array."))), DescribeRole.Theorem))));
}
