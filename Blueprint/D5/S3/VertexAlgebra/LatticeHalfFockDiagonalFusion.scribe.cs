using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockDiagonalFusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockDiagonalFusion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal fusion of native half-lattice kernels", H("Actual Diagonal Fusion"), Blocks(
            Paragraph(Text("The lattice datum has arbitrary signature. Polynomial creation and translation act on the original unrestricted oscillator algebra. Every diagonal sum is finite on its actual input before multiplication, reindexing or tensor extension.")),
            Describe.Lean(DescribeId.Create("creation-exponential-add"),
                DeclarationHandle.Create(Prefix + "creation_exponential_add"), H("Creation exponential"),
                StatementSource.FromAuthor(Disp(Call("CreationAdd", F.Id("D"), F.Id("a"), F.Id("b")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The creation exponential for a+b is the product of the original creation exponentials. The original coefficient-recurrence uniqueness theorem applies to their actual differentiated series and their equal constant coefficients."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("creation-coefficient-add"),
                DeclarationHandle.Create(Prefix + "creation_coefficient_add"), H("Integer convolution"),
                StatementSource.FromAuthor(Disp(Call("CreationConvolution", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("T")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every signed integer T, the convolution of the two creation coefficient families is the charge-sum coefficient. Negative T gives the empty supported sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-kernel-diagonal-fusion"),
                DeclarationHandle.Create(Prefix + "common_kernel_diagonal_fusion"), H("Arbitrary polynomial fusion"),
                StatementSource.FromAuthor(Disp(Call("KernelDiagonalFusion", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("T"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Summing commonKernel(a,b,E,T-E)p over its finite diagonal gives the coefficient convolution of the original charge-(a+b) translated polynomial. The creator step combines both original Gram contractions, not a vacuum specialization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-common-kernel-diagonal-fusion"),
                DeclarationHandle.Create(Prefix + "tensor_common_kernel_diagonal_fusion"), H("Actual tensor fusion"),
                StatementSource.FromAuthor(Disp(Call("TensorKernelDiagonalFusion", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b"), F.Id("T"), F.Id("v")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For IsUnit D.G.det and every actual target v, tensor fusion retains epsilon(D,a,b) and the actual chosen ground representation. Its oscillator coefficient has index T-chargeNorm(a+b). No substituted ground space, positivity hypothesis or assumed fusion law is used."))), DescribeRole.Theorem))));
}
