using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class RingActionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ring Actions", H("Ring Actions"),
        Blocks(
            Paragraph(Text("Functoriality of adic completion; extending monoid actions to completions, localisations, Witt vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/RingActions.isSMulRegular_completion"),
                H("isSMulRegular_completion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If multiplication by the natural number n is injective on the R-module X, then it is injective on the n-adic completion of X.")))))));
}
