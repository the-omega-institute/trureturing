using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class SemiInvariantNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semi Invariant Norm", H("Semi Invariant Norm"),
        Blocks(
            Paragraph(Text("for products of polynomials, weights add and norm bounds multiply.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/SemiInvariantNorm.HasWeightNormLe"),
                H("HasWeightNormLe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("F is the polynomial of some coordinate vector ξ of weight κ, and, if p holds, ξ has squared norm at most b.")))))));
}
