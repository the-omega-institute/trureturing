using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockProductKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native bivariate half-Fock product kernel",
        H("Finite Native Common Kernel"),
        Blocks(
            Paragraph(Text("D is any finite-rank integral symmetric even-diagonal lattice datum; a,b are arbitrary charges. "
                + "The oscillator input p is an arbitrary finite polynomial, not a homogeneous or truncated state. "
                + "S_ab is the actual substitution X(i,k) -> C(X(i,k))-C(B(a,e_i))X0^(2k+1)-C(B(b,e_i))X1^(2k+1). "
                + "J_ab[u,v](p) sums its actual finite support eta, multiplying coeff_eta(S_ab(p)) by "
                + "halfCreationCoeff(a,u+eta0) halfCreationCoeff(b,v+eta1). Negative creation indices are zero. "
                + "The bivariate convolution is formed from the delivered native creation coefficients and finite polynomial support.")),
            Describe.Lean(DescribeId.Create("native-translation-composition"),
                DeclarationHandle.Create(Prefix + "pair_translation_composition"), H("Actual finite translation composition"),
                StatementSource.FromAuthor(Disp(Call("PairTranslationComposition", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Apply the delivered native halfTranslatedPolynomial for b, then translate its oscillator coefficients "
                    + "by S_a0 and evaluate its formal variable at X1. The result is exactly S_ab(p). "
                    + "Constants, polynomial addition and multiplication by each oscillator variable prove this equality. "
                    + "This finite composition is used in the two-coordinate creator recurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-kernel-constant"),
                DeclarationHandle.Create(Prefix + "kernel_constant"), H("Constant readout"),
                StatementSource.FromAuthor(Disp(Call("ConstantKernel", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("u"), F.Id("v"), F.Id("c")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every complex c, J_ab[u,v](C(c))=C(c) halfCreationCoeff(a,u) halfCreationCoeff(b,v). "
                    + "The constant readout supplies the vacuum step of the ordered-product and branch-exchange proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-kernel-creator"),
                DeclarationHandle.Create(Prefix + "kernel_creator"), H("Two-coordinate recurrence"),
                StatementSource.FromAuthor(Disp(Call("CreatorKernel", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("u"), F.Id("v"), F.Id("p"), F.Id("i")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For each native index i=(colour,k), put omega_i=2k+1. Then "
                    + "J_ab[u,v](X_i p)=X_i J_ab[u,v](p)-B(a,e_colour) J_ab[u+omega_i,v](p) "
                    + "-B(b,e_colour) J_ab[u,v+omega_i](p). This recurrence is consumed by the universal "
                    + "branch-exchange and actual native product proofs, with no factor two in either translation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-rectangular-support"),
                DeclarationHandle.Create(Prefix + "common_kernel_rectangular_support"), H("Rectangular lower bounds"),
                StatementSource.FromAuthor(Disp(Call("RectangularSupport", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every D,a,b,p there exist integers A,B such that for all integers u,v, "
                    + "u<A or v<B implies J_ab[u,v](p)=0. One can take A=-sup_eta eta0 and B=-sup_eta eta1 "
                    + "over the actual finite support of S_ab(p). Each supported summand then has a negative "
                    + "native creation index. The zero polynomial and empty support are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-ordered-support"),
                DeclarationHandle.Create(Prefix + "common_kernel_ordered_finite_support"), H("Both ordered rays are finite"),
                StatementSource.FromAuthor(Disp(Call("FiniteOrderedRays", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("u"), F.Id("v"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every D,a,b,u,v,p, both r -> J_ab[u+r,v-r](p) and r -> J_ab[u-r,v+r](p), r in N, "
                    + "have finite support. The second coordinate bounds the first ray; the first coordinate bounds the second. "
                    + "These statewise bounds precede every finsum distribution or reindexing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-branch-exchange"),
                DeclarationHandle.Create(Prefix + "common_kernel_branch_exchange"), H("Branch exchange"),
                StatementSource.FromAuthor(Disp(Seq(Call("J", F.Id("a"), F.Id("b"), F.Id("u"), F.Id("v"), F.Id("p")), Eq,
                    Call("J", F.Id("b"), F.Id("a"), F.Id("v"), F.Id("u"), F.Id("p"))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every D,a,b,u,v,p, J_ab[u,v](p)=J_ba[v,u](p). Constants use commutativity of actual creation "
                    + "polynomials; arbitrary input follows from polynomial addition and the actual two-coordinate creator recurrence."))), DescribeRole.Theorem),
            Paragraph(Text("Classical twisted-lattice construction, with zero novelty claim. "
                + "This kernel is not a twisted Jacobi certificate, a physical iterate, or an orbifold reconstruction. "
                + "The corresponding charged tensor fields use the actual ground representation selected from "
                + "actual_twisted_ground_representation D hu, with hu:IsUnit D.G.det; the oscillator kernel itself needs no hu.")))));
}
