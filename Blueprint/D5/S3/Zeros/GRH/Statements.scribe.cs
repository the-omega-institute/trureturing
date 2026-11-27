using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH;

internal sealed class StatementsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Statements", H("Statements"),
        Blocks(
            Paragraph(Text("Four formulations of the zero statements")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Statements.DirichletLNonvanishingRightOfHalf"),
                H("DirichletLNonvanishingRightOfHalf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The half-plane formulation quantifies over every character of every positive modulus. At a point with real part greater than one half, the disjunction that the character is nonprincipal or that the point differs from one excludes precisely the principal pole.")))))));
}
