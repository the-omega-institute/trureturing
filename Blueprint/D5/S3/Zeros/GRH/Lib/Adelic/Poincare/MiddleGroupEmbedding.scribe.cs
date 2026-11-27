using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Poincare;

internal sealed class MiddleGroupEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Middle Group Embedding", H("Middle Group Embedding"),
        Blocks(
            Paragraph(Text("Block embedding of U(k) onto the reductive part H of the Bessel subgroup.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Poincare/MiddleGroupEmbedding.toBesselH"),
                H("toBesselH"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The embedding of the unitary group of the identity form on A^κ into the unitary group of the whole space with middle form Shape.middleGram N, acting on X₀ and fixing the other basis vectors.")))))));
}
