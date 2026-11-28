using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class ChainNormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chain Norms", H("Chain Norms"),
        Blocks(
            Paragraph(Text("Chain of theta lifts is injective; its inner product and level index count.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/ChainNorms.iotaAtLevel_injective"),
                H("iotaAtLevel_injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For every twist ϑ whose first m powers are twists, the composite ι_ϑ of the m theta lifts from U(Y₀) to the definite U(Y_m) is injective on forms of principal level g on U(Y₀).")))))));
}
