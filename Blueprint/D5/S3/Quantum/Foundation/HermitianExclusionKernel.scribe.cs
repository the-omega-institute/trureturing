using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class HermitianExclusionKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the complete complex positive semidefinite cone, exclusion by any proper real-linear effect equals the density face annihilating the confirmed unit vector.",
        H("Full Hermitian exclusion and orthogonal support"),
        Blocks(
            Paragraph(Text("Let J be any finite index type with decidable equality. The carrier is the real inner product space of all complex Hermitian matrices indexed by J. Its cone consists of all positive semidefinite matrices, and its unit is the trace. The normalized base contains every positive semidefinite trace-one matrix. Effects range over every real-linear functional f satisfying 0 <= f(Y) <= trace(Y) for every positive semidefinite Y. No selected measurements or restricted effect domain is used.")),
            Entry("full-cone", "cone", "The entire positive semidefinite cone",
                "The cone is PointedCone.positive on the original Hermitian carrier, with its Loewner order.", DescribeRole.Definition),
            Entry("trace-unit", "unit", "The original trace unit",
                "The unit is the real-linear pairing with the identity matrix. HermitianMat.one_inner identifies it with the trace on every Hermitian matrix.", DescribeRole.Definition),
            Entry("positive-representative", "positive_representative", "Every positive original functional has a positive representative",
                "Every real-linear functional nonnegative on the entire native PSD cone is pairing with a PSD Hermitian matrix on the entire carrier. The original Riesz proof tests every native outer product. This same declaration supplies the whole-effect model application of the original state-cover theorem.", DescribeRole.Theorem),
            Entry("exclusion-kernel", "exclusion_iff_kernel", "The entire exclusion is an orthogonal support face",
                "For every complex Euclidean vector v of norm one and every Hermitian matrix X, X belongs to the original exclusion of rankOne(v) if and only if X is positive semidefinite, trace(X)=1, and Xv=0. The exclusion quantifies over every original proper real-linear effect f, with f(rankOne(v))=1 and f(X)=0. X may have any rank, and there is no prior choice of an orthogonal face or compressed coordinate domain.", DescribeRole.Theorem),
            Paragraph(Text("Finite-dimensional real Riesz representation writes the chosen functional as pairing with a Hermitian matrix A. Testing positivity on every outer product shows A is positive semidefinite; the upper trace bound similarly shows I-A is positive semidefinite. Acceptance of the unit vector makes (I-A)v=0, hence Av=v. Zero pairing of A and X puts the support of A in the kernel of X. Since v is in the range of A, Xv=0. This argument uses the whole mixed matrix X without replacing it by a rank-one state. Conversely, pairing with rankOne(v) is an original proper functional by positivity and the trace-product bound; it accepts rankOne(v) and vanishes on X when Xv=0.")),
            Paragraph(Text("This support characterization applies in every finite complex dimension. It does not construct affine ball coordinates, classify all original extreme points, or assert a complete three-dimensional exclusion-ball model. It makes no claim about physical preparation procedures or literature priority.")))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/Quantum/Foundation/HermitianExclusionKernel." + declaration),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);
}
