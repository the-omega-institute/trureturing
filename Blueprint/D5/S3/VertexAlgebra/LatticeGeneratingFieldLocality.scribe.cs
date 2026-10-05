using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeGeneratingFieldLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula T => F.Id("t");
    private static Formula J => F.Id("j");
    private static Formula D => F.Id("d");
    private static Formula P => F.Id("p");
    private static Formula C(Formula a, Formula t) => Call("c", a, t);
    private static Formula Single() => Call("single", D, P);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("G"), Comma, A, Comma, B, Comma, Sp,
        Parenthesized(Seq(Forall, Sp, T, InMacro, Sp, Z, Comma, Sp,
            Call("Hom", C(B, T), Call("toNat", T)))), Sp, Land, Sp,
        Parenthesized(Seq(Forall, Sp, T, InMacro, Sp, Z, Comma, Sp,
            J, InMacro, Sp, N, Comma, Sp,
            Call("coeff", J, Call("T", A, C(B, T))), Eq,
            Call("h", Call("B", A, B), J), Sp, C(B, Seq(T, Minus, J)))), Sp, Land, Sp,
        Parenthesized(Seq(Forall, Sp, F.Id("k"), InMacro, Sp, Z, Comma, Sp,
            D, InMacro, Sp, F.Id("L"), Comma, Sp, P, InMacro, Sp, F.Id("P"), Comma, Sp,
            Call("F", A, F.Id("k"), Single()), Eq,
            Call("rawSingle", A, F.Id("k"), D, P))), Sp, Land, Sp,
        Parenthesized(Seq(Forall, Sp, F.Id("u"), Comma, F.Id("v"), InMacro, Sp, Z,
            Comma, Sp, D, InMacro, Sp, F.Id("L"), Comma, Sp,
            P, InMacro, Sp, F.Id("P"), Comma, Sp,
            Call("K", A, B, F.Id("u"), F.Id("v"), Single()), Eq,
            Call("commonKernelSingle", A, B, F.Id("u"), F.Id("v"), D, P)))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial translation of the actual lattice creation coefficients gives the binomial contraction.",
        H("Actual Lattice Creation Coefficients"),
        Blocks(
            Paragraph(Text("Let r be any natural number, including zero, and G any "
                + "symmetric integral r by r matrix with even diagonal. No positivity "
                + "is assumed. Charges are functions Fin(r) to Z, oscillator variables "
                + "are indexed by Fin(r) times N, and variable (i,n) has weight n+1. "
                + "The polynomial algebra P is over C and the actual carrier is "
                + "V, the finite-support functions from charges to P. The bilinear "
                + "form is B(alpha,beta)=sum_i,j alpha_i G_ij beta_j.")),
            Paragraph(Text("For charge beta, S_beta has constant coefficient zero "
                + "and positive coefficient q equal to q^(-1) times "
                + "sum_i beta_i X(i,q-1). Set C_beta=exp.subst(S_beta), "
                + "using the formal power-series exponential over P. Its integer "
                + "creation coefficient c_beta(t) is zero for t<0 and otherwise "
                + "the t.toNat coefficient. Translation T_alpha is the complex "
                + "algebra map sending X(i,n) to X(i,n)-B(alpha,e_i) U^(n+1) "
                + "in P[U]. These are the actual exponential and polynomial "
                + "translation, rather than arbitrary coefficients satisfying "
                + "a contraction hypothesis.")),
            Describe.Lean(
                DescribeId.Create("actual-creation-coefficient-transport"),
                DeclarationHandle.Create(Prefix + "actual_creation_coefficient_transport"),
                H("Every integer creation index and polynomial translation coefficient"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every such G and all charges alpha,beta, "
                        + "written a,b in the display, Hom is weighted homogeneity "
                        + "for the weights n+1, toNat is integer truncation at zero, "
                        + "and h(B(a,b),j) denotes h_b(j) with b=B(a,b). "
                        + "c_beta(t) is weighted homogeneous of degree t.toNat "
                        + "for every integer t. For every integer t and natural j, "
                        + "coeff_j(T_alpha(c_beta(t))) = h_b(j) c_beta(t-j), "
                        + "where b=B(alpha,beta) and h_b(j) is coeff_j of "
                        + "rescale(-1)(binomialSeries(C,b)), with its parameter "
                        + "ring explicitly Z. Thus h_b(j)=(-1)^j choose(b,j); "
                        + "negative b uses integer binomial coefficients, without "
                        + "a Laurent-series integer power.")),
                    Paragraph(Text("The proof differentiates the actual substituted "
                        + "exponential and proves the homogeneous grading by "
                        + "strong induction on its coefficient recurrence. After "
                        + "translation, the derivative difference has coefficient "
                        + "-B(alpha,beta) U^(n+1). Multiplication by 1-Uw converts "
                        + "this to a constant polynomial coefficient. The "
                        + "descending-Pochhammer recurrence for integer choose "
                        + "gives the same differential equation for the binomial "
                        + "factor. Equality of constant coefficients and strong "
                        + "induction identify the two actual series. Extracting "
                        + "their finite antidiagonal convolution proves the "
                        + "displayed translation coefficient equality.")),
                    Paragraph(Text("The same conjunction proves that the raw field "
                        + "and common-kernel monomial basis extensions agree "
                        + "with their prescribed formulas on every single(delta,p), "
                        + "for every charge delta, polynomial p and all integer "
                        + "indices. These equalities use algebra-map linearity "
                        + "and finite coefficient sums; they are not assumed "
                        + "to hold by definition. The explicit cocycle uses the "
                        + "lower-triangular exponent and G_ii/2 diagonal exponent, "
                        + "each interpreted by integer parity.")),
                    Paragraph(Text("The actual raw family is packaged by "
                        + "VertexOperator.of_coeff. A finite polynomial "
                        + "translation support gives a lower Laurent bound on "
                        + "each monomial state, and finite monomial and charge "
                        + "supports give a statewise lower bound for every "
                        + "carrier vector. Normalized mode m corresponds to "
                        + "raw Laurent power -m-1.")),
                    Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1 "
                        + "(2004-02-19), section 4.1, printed pages 8-9, "
                        + "equation (4.12) specifies the exponential lattice "
                        + "field, and (4.14) uses its annihilation-creation "
                        + "contraction in the ordered product. The Library "
                        + "note records the inspected arXiv version and "
                        + "published DOI 10.1142/9789812702562_0001. This "
                        + "coefficient theorem is classical formalization; "
                        + "it does not establish the two common-kernel composed "
                        + "mode formulas, uniform locality, lattice Jacobi, "
                        + "a Monster construction, full CFT, string theory "
                        + "or an AdS/CFT bridge."))),
                DescribeRole.Theorem))));
}
