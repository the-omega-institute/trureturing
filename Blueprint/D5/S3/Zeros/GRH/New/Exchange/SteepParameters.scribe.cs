using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class SteepParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Steep Parameters", H("Steep Parameters"),
        Blocks(
            Paragraph(Text("The chosen parameters satisfy the steepness hypothesis of the Laplace-method lemma.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/SteepParameters.exists_isSteep"),
                H("exists_isSteep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For either grid z, one ordering e of the indices gives the signs and parameter of the node (0, 0), offset 0, the shape IsSteep with bound w₀(τ) = Data.w 0 τ at every infinite place τ.")))))));
}
