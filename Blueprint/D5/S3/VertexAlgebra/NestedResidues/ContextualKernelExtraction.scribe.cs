using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class ContextualKernelExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite contextual Hahn convolution fibers for signed collision kernels.",
        H("Supported contextual kernel extraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nested-residues-contextual-kernel-extraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction.contextual_kernel_extraction"),
                H("Every complete Hahn convolution fiber has finite support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality")),
                Blocks(
                    Paragraph(Text("For any field K, any prefix and suffix lengths pre and post, any integer diagonal exponent r, any supported Hahn series W and any output exponent g, the coefficient at g of contextPair(K,pre,post,kernelZX(K,r)) times W is its natural-index binomial convolution. Its summand at j is (-1)^j choose(r,j) times the coefficient of W at g-pairIndex(pre,post,(j,r-j)). The theorem proves finite support of that convolution and its exact coefficient equation together. Every spectator coordinate remains fixed.")),
                    Paragraph(Text("The nonzero terms embed injectively in the finite full Hahn multiplication antidiagonal. Conversely, the binomial support parametrization represents every nonzero antidiagonal term. This gives a finite bijection without a cutoff on either ordered part of an intermediate field.")),
                    Paragraph(Text("The nested Q fiber calculations use this coefficient identity inside the complete inner residue. Identification of complete outer Q residues with the finite same-numerator Taylor coordinates requires further local-coordinate equalities; this theorem establishes no such outer identification."))),
                DescribeRole.Theorem))));
}
