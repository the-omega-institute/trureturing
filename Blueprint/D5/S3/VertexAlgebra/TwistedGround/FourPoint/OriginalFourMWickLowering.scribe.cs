using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMWickLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wick expansion of the lowering word at one puncture",
        H("Central contractions and surviving creators"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-m-wick-lowering-pair-weight"),
                DeclarationHandle.Create(Prefix + "pairWeight"),
                H("Evaluated central pair weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluate the central pair polynomial at a complex lowering parameter and "
                    + "take its constant oscillator coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-m-wick-lowering-eval-word-partition"),
                DeclarationHandle.Create(Prefix + "eval_word_partition"),
                H("Partition into contraction endpoints and surviving creators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant, a finite label type with an assigned "
                    + "oscillator index at each label, and any word and complex parameter, the evaluated lowering "
                    + "word is a sum over ordered partitions of its positions. The first subword contributes the "
                    + "zero-mean Wick value of the evaluated pair weights, embedded as a constant oscillator "
                    + "polynomial. The second contributes the product of evaluated creators. The recursion deletes "
                    + "paired positions individually, so repeated labels and modes retain their multiplicities."))),
                DescribeRole.Theorem))));
}
