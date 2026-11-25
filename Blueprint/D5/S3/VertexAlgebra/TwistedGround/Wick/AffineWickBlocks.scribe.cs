using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Wick;

internal sealed class AffineWickBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wick evaluation on independent covariance blocks",
        H("Restriction to the occurrence word"),
        Blocks(
            Describe.Lean(DescribeId.Create("affine-wick-blocks-wick-congr-on"),
                DeclarationHandle.Create(Prefix + "wick_congr_on"),
                H("Covariances agreeing along the word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the same mean, two covariances give the same Wick value on a word whenever "
                    + "they agree on every pair of labels occurring in it. The condition is inherited by the shorter "
                    + "words in the recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-wick-blocks-wick-block"),
                DeclarationHandle.Create(Prefix + "wick_block"),
                H("Factorization across two blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite label type, a symmetric covariance that vanishes between opposite "
                    + "values of a Boolean block predicate has a zero-mean Wick value equal to the product of the "
                    + "two values on the filtered subwords. In the covariance convolution, a position assigned to "
                    + "the wrong block has no eligible pair, so only the partition selected by the predicate can contribute."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-wick-blocks-wick-blocks"),
                DeclarationHandle.Create(Prefix + "wick_blocks"),
                H("Factorization over a finite set of blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite label type, take a symmetric covariance that vanishes between "
                    + "different slots and a finite set of slots with decidable equality containing the slot of "
                    + "each word entry. The zero-mean Wick value is the product of the values on the subwords "
                    + "filtered by each slot. Induction on the slot set applies the two-block formula to "
                    + "separate one slot at a time."))),
                DescribeRole.Theorem))));
}
