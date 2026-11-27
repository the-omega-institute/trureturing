using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class HyperbolicSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic Space", H("Hyperbolic Space"),
        Blocks(
            Paragraph(Text("Framed hyperbolic space; matrices unitary at infinity and integral at finite places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/HyperbolicSpace.IsOrthoIntegral"),
                H("IsOrthoIntegral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The condition on an adelic matrix M that M_τ* M_τ = 1 at every infinite place τ and that all entries have integral finite part.")))))));
}
