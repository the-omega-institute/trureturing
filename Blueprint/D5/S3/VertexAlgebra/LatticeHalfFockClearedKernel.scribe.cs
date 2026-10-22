using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockClearedKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical differences of supported native common-kernel expansions", H("Cleared Kernel Action"), Blocks(
            Paragraph(Text("For arbitrary D,a,b, an unrestricted oscillator polynomial p and a scalar power series h, "
                + "E_h[k,l](p)=sum_(r>=0) coeff_r(h) J_ab[k+r,l-r](p). "
                + "The actual rectangular kernel bounds prove finite support before any splitting or subtraction. "
                + "The physical difference is D2 F[k,l]=F[k-2,l]-F[k,l-2]. "
                + "Only the generic finite-support splitting supplier is reused; ordinary cover delta is not a twisted Jacobi certificate.")),
            Describe.Lean(DescribeId.Create("physical-difference-expansion"),
                DeclarationHandle.Create(Prefix + "physical_difference_expansion"), H("One physical difference"),
                StatementSource.FromAuthor(Disp(Call("PhysicalDifferenceExpansion", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("h"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "D2 E_h[k,l]=E_((1-s^2)h)[k-2,l]. The proof splits off the first two finite-support terms "
                    + "and uses native PowerSeries coefficients of X^2 h, with every shifted sum proved finite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-cleared-kernel"),
                DeclarationHandle.Create(Prefix + "native_cleared_kernel_expansion"), H("Native physical clearing"),
                StatementSource.FromAuthor(Disp(Call("NativeClearedKernel", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "At N=abs B(a,b), D2^N E_hg[k,l]=E_Pg[k-2N,l], using the exact two-branch scalar identity. "
                    + "This common-kernel statement alone does not prove actual charged tensor locality. "
                    + "Actual charged locality also uses the ordered products, polynomial reversal and actual ground signs. "
                    + "No twisted Jacobi, complete orbifold or string/AdS realization follows. Classical provenance, zero novelty claim."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-cleared-kernel-exchange"),
                DeclarationHandle.Create(Prefix + "native_cleared_kernel_exchange"), H("Exchange of the cleared native kernels"),
                StatementSource.FromAuthor(Disp(Call("ClearedKernelExchange", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("p"), F.Id("k"), F.Id("l")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For all D,a,b,p,k,l and N=abs B(a,b), D2^N E_ab[k,l] equals D2^N E_ba[l,k]. "
                    + "The fixed-degree reciprocal polynomial and the actual common-kernel branch exchange prove this equality "
                    + "by a finite coefficient reversal. No equality of the unregularized iota expansions is asserted."))), DescribeRole.Theorem))));
}
