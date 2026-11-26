using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class LiftCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lift Characters", H("Lift Characters"),
        Blocks(
            Paragraph(Text("Column level at N read as conjugated mirabolic group; restriction keeps valuation, size. Index bound at N for preimage of the lattice under the Gauss-sum operator power. Splitting characters of the chain: unramified above the level prime, double splitting.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/LiftCharacters.spaceChar_rankTwist"),
                H("spaceChar_rankTwist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the character ν of lift i and twist ϑ, applying rankTwist for X_j and then AutChar.spaceChar in rank |X_j| gives the Hecke character x ↦ ν(x/x̄).")))))));
}
