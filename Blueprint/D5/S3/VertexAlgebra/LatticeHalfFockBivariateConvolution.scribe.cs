using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockBivariateConvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native coefficient convolution supplier interfaces",
        H("Native coefficient convolution supplier interfaces"),
        Blocks(
            Paragraph(Text("The generic coefficientConvolution and bivariateCoefficientConvolution definitions and proof bodies are the completed LatticeActualProductKernel supplier interfaces. They are installed in that original namespace without replacing the existing ordinary lattice convolution and pairConvolution declarations.")),
            Paragraph(Text("LatticeHalfFockOrderedProducts consumes the one-variable coefficient interface. LatticeHalfFockProductKernel consumes the bivariate coefficient interface to prove the actual half-creation kernel support. These are existing reusable supplier proofs, not additional mathematical novelty or separate bind-only formalization targets.")))));
}
