using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeGeneratingFieldProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeGeneratingFieldProducts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula L => F.Id("l");
    private static Formula V => F.Id("v");
    private static Formula J => F.Id("j");
    private static Formula Pairing => Call("B", A, B);
    private static Formula Factor => Call("h", Pairing, J);
    private static Formula Forward => Seq(Factor, Sp,
        Call("K", A, B, Seq(K, Minus, Pairing, Plus, J), Seq(L, Minus, J), V));
    private static Formula Reverse => Seq(Factor, Sp,
        Call("K", A, B, Seq(K, Minus, J), Seq(L, Minus, Pairing, Plus, J), V));
    private static Formula Parens(Formula f) => Seq(Open, f, Close);

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("G"), Comma, A, Comma, B, Comma, K, Comma, L, Comma, V, Comma, Sp,
        Call("Finite", Call("supp", Call("jmap", J, Forward))), Sp, Land, Sp,
        Call("Finite", Call("supp", Call("jmap", J, Reverse))), Sp, Land, Sp,
        Parens(Seq(Call("F", A, K, Call("F", B, L, V)), Eq,
            Call("epsilon", A, B), Sp, Call("finsum", J, Forward))), Sp, Land, Sp,
        Parens(Seq(Call("F", B, L, Call("F", A, K, V)), Eq,
            Call("epsilon", B, A), Sp, Call("finsum", J, Reverse)))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both ordered actual lattice-field products use the same two-variable kernel, with finite sums on each recipient.",
        H("Actual Lattice Field Products"),
        Blocks(
            Paragraph(Text("Let r be any natural number, including zero. Let G be any "
                + "symmetric integral r by r matrix with even diagonal, without a "
                + "positivity hypothesis. Charges are functions Fin(r) to Z. The "
                + "oscillator algebra P is the complex multivariate polynomial "
                + "algebra on Fin(r) times N, and V is the space of finite-support "
                + "charge-indexed functions with values in P. Write B(alpha,beta) "
                + "for the integral bilinear pairing.")),
            Paragraph(Text("F_alpha(k) denotes the actual raw Laurent coefficient "
                + "of the exponential charge-changing lattice field, using the "
                + "creation exponential, polynomial annihilation translation, "
                + "and lower-triangular parity cocycle epsilon. Its normalized "
                + "mode m has raw index k=-m-1. The common kernel K(alpha,beta)(u,v) "
                + "uses the translated pair polynomial with variables U,W: "
                + "X(i,n) maps to X(i,n)-B(alpha,e_i) U^(n+1)-B(beta,e_i) W^(n+1). "
                + "On single(delta,p), its summand at exponent pair e has "
                + "coefficient q_e c_alpha(u-B(alpha,delta)+e_0) "
                + "c_beta(v-B(beta,delta)+e_1), with charge alpha+beta+delta "
                + "and prefactor epsilon(alpha+beta,delta).")),
            Describe.Lean(
                DescribeId.Create("actual-lattice-field-products"),
                DeclarationHandle.Create(Prefix + "actual_lattice_field_products"),
                H("Both products on every recipient and every pair of integer indices"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges alpha,beta, all integers k,l "
                        + "and every v in V, both displayed summands have finite "
                        + "support as functions of the natural index j. Here "
                        + "h_b(j) is coeff_j of rescale(-1)(binomialSeries(C,b)), "
                        + "with parameter ring Z and b=B(alpha,beta). Thus "
                        + "h_b(j)=(-1)^j choose(b,j), including negative integer b. "
                        + "The two product equations are "
                        + "F_alpha(k)(F_beta(l)v)=epsilon(alpha,beta) "
                        + "sum_j h_b(j) K(alpha,beta)(k-b+j,l-j)v and "
                        + "F_beta(l)(F_alpha(k)v)=epsilon(beta,alpha) "
                        + "sum_j h_b(j) K(alpha,beta)(k-j,l-b+j)v. "
                        + "The notation jmap in the display forms the function "
                        + "of j, and finsum sums its finite support in the "
                        + "recipient space V.")),
                    Paragraph(Text("For single(delta,p), write q for the "
                        + "translated pair polynomial. A nonzero forward "
                        + "summand requires j<=l-B(beta,delta)+sup_e(e_1), "
                        + "where e ranges over q.support. The reverse bound "
                        + "is j<=k-B(alpha,delta)+sup_e(e_0). A negative "
                        + "upper bound forces every summand to vanish. "
                        + "These bounds depend on the recipient; finite "
                        + "charge supports extend finiteness to arbitrary "
                        + "v. No uniform polynomial or recipient cutoff "
                        + "is assumed.")),
                    Paragraph(Text("Nested polynomial maps identify translating "
                        + "the beta-translated polynomial by alpha with the "
                        + "same pair polynomial. The actual creation-coefficient "
                        + "transport identity gives the binomial contraction "
                        + "for every integer creation index, including negative "
                        + "indices. Applying coefficient linear maps and "
                        + "exchanging sums with already finite support yields "
                        + "the first product. Bilinear additivity and cocycle "
                        + "multiplicativity match its charge shifts and scalar "
                        + "factors. Swapping the pair variables proves kernel "
                        + "symmetry and gives the second product.")),
                    Paragraph(Text("The classical source is Bakalov-Kac, "
                        + "arXiv math/0402315v1 (2004-02-19), section 4.1, "
                        + "printed pages 8-9, equations (4.12) and (4.14), "
                        + "with published DOI 10.1142/9789812702562_0001. "
                        + "The Library note records the inspected version "
                        + "and the limits of the FLM citation. This theorem "
                        + "does not establish mutual locality, a full lattice "
                        + "VOA constructor, the Leech or Monster construction, "
                        + "a full CFT, string theory, or an AdS/CFT bridge.")))))));
}
