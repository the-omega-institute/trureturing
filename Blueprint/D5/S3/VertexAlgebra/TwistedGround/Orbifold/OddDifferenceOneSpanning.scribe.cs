using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OddDifferenceOneSpanningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a positive-definite lattice, degreewise generation by homogeneous representatives and minus-two "
            + "products puts homogeneous mode words in the span of strictly increasing representative words.",
        H("Difference-one straightening"),
        Blocks(
            Describe.Lean(DescribeId.Create("word-mem-strict-span"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Orbifold/"
                    + "OddDifferenceOneSpanning.word_mem_strictSpan"),
                H("Terminating straightening of homogeneous words"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three inductions use total source weight, word length, and the deficit "
                    + "of the square sum from an upper bound at fixed index sum. Sort large-index terms and apply "
                    + "truncation at the seed before comparing square sums."))), DescribeRole.Theorem))));
}
