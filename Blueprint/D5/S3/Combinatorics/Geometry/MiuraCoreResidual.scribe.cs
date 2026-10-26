using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreResidual.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("The exact residual class is preserved"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracoreresidual-0"),
                DeclarationHandle.Create(Prefix + "cellOnSide"), H("One physical side"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Side membership uses the actual first or last row or column of the finite rectangle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoreresidual-1"),
                DeclarationHandle.Create(Prefix + "cellExpand_on_side"), H("Boundary membership survives deletion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each of the four sides separately, a surviving cell lies on that side before deletion exactly when it lies on the corresponding physical side afterward."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreresidual-2"),
                DeclarationHandle.Create(Prefix + "all_minima_side_iff"), H("The source common-side condition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The one-based source predicate that every minimum lies on one specified side agrees with pointwise physical side membership of all strict minima."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreresidual-3"),
                DeclarationHandle.Create(Prefix + "contractAt_minima_card"), H("The number of minima is unchanged"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Signed internal frozen deletion preserves the exact cardinality of the set of strict minima."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreresidual-4"),
                DeclarationHandle.Create(Prefix + "contractAt_maxima_card"), H("The number of maxima is unchanged"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Signed internal frozen deletion separately preserves the exact cardinality of the set of strict maxima."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreresidual-5"),
                DeclarationHandle.Create(Prefix + "contractAt_all_minima_side_iff"), H("The same side contains all minima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each specified physical side, all minima lie on that side before signed deletion exactly when all contracted minima lie on the corresponding side."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreresidual-6"),
                DeclarationHandle.Create(Prefix + "contractAt_residual"), H("The exact residual class is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every split a,b and every actual normalized residual height array, deleting an internal frozen column preserves normalization, both exact extremum counts, and the absence of one common side containing all minima."))), DescribeRole.Theorem))));
}
