using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOrderedProductsDocument : IScribeDocumentDefinition
{
    private const string Ordered = "D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");
    private static Formula V(string name) => F.Id(name);
    private static Formula Bound(string name, Formula type) => Seq(V(name), Colon, type);
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula CommonParameters => Seq(
        Bound("D", V("LatticeData")), Comma, Sp,
        Bound("a", Call("Charge", V("D"))), Comma, Sp,
        Bound("b", Call("Charge", V("D"))));
    private static Formula Indices => Seq(Bound("s", Z), Comma, Sp, Bound("t", Z));
    private static Formula Polynomial => Bound("p", Call("Oscillator", V("D")));
    private static Formula K(Formula s, Formula t, Formula p) =>
        Call("K", V("D"), V("a"), V("b"), s, t, p);
    private static Formula Forward(Formula p) => Call("finsum", Bound("d", N),
        Seq(Call("kappa", V("D"), V("a"), V("b"), V("d")), Sp,
            K(Seq(V("s"), Plus, V("d")), Seq(V("t"), Minus, V("d")), p)));
    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string prose) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Ordered + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full forward ordered products of native half-Fock coefficients",
        H("Native Half-Fock Forward Ordered Products"),
        Blocks(
            Paragraph(Text("Let D be any integral symmetric even-diagonal lattice datum, with arbitrary finite rank. "
                + "The charges a,b are arbitrary integer-valued lattice vectors. The oscillator algebra is the entire "
                + "MvPolynomial(Fin(D.rank) times N,C), including every inhomogeneous polynomial. No determinant, "
                + "positivity, charge-pairing sign, or mode cutoff is assumed. Put q(a)=B(a,a) and omega(i,j)=2j+1. "
                + "All external indices s,t range independently over the integers.")),
            Paragraph(Text("Write C_a[n]=halfCreationCoeff D a n, with C_a[n]=0 for n<0, "
                + "and Q_a(p)=halfTranslatedPolynomial D a p. Q_a replaces X(i,j) by "
                + "X(i,j)-B(a,e_i)x^(2j+1). The bivariate pairTranslation replaces it by "
                + "X(i,j)-B(a,e_i)x^(2j+1)-B(b,e_i)y^(2j+1). "
                + "pairConvolution at (s,t) sends a monomial c x^u y^v to c C_a[s+u] C_b[t+v]. "
                + "Their composition is the complex-linear commonKernel, denoted K(D,a,b,s,t,p). "
                + "The two translation variables represent inverse cover coordinates, accounting for the positive offsets.")),
            Theorem("pair-translation-composition", "pair_translation_composition", "Successive translations",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Polynomial, Comma, Sp,
                    Call("secondTranslationLift", V("D"), V("a"), Call("Q", V("D"), V("b"), V("p"))),
                    Eq, Call("pairTranslation", V("D"), V("a"), V("b"), V("p"))),
                "The complete parameters are D,a,b,p as above. secondTranslationLift applies the first translation "
                + "to every coefficient of Q_b(p) and sends its polynomial variable to y. This equals the simultaneous "
                + "pairTranslation for every polynomial, by equality on constants, sums and multiplication by each generator."),
            Theorem("kernel-constant", "kernel_constant", "Kernel on constants",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Indices, Comma, Sp,
                    Bound("c", Seq(Mathbb, Grp(V("C")))), Comma, Sp,
                    K(V("s"), V("t"), Call("C", V("c"))), Eq,
                    Call("C", V("c")), Sp, Call("creation", V("D"), V("a"), V("s")), Sp,
                    Call("creation", V("D"), V("b"), V("t"))),
                "For every complex scalar c, the kernel of C(c) is C(c) C_a[s] C_b[t]. "
                + "This follows from the constant bivariate monomial and is used in the vacuum contraction calculation."),
            Theorem("kernel-creator", "kernel_creator", "Both creator shifts",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Indices, Comma, Sp, Polynomial, Comma, Sp,
                    Bound("i", Call("Index", V("D"))), Comma, Sp,
                    K(V("s"), V("t"), Seq(Call("X", V("i")), V("p"))), Eq,
                    Call("X", V("i")), K(V("s"), V("t"), V("p")), Minus,
                    Call("B", V("a"), Call("unitCharge", V("D"), Call("fst", V("i")))), Sp,
                    K(Seq(V("s"), Plus, Call("omega", V("D"), V("i"))), V("t"), V("p")), Minus,
                    Call("B", V("b"), Call("unitCharge", V("D"), Call("fst", V("i")))), Sp,
                    K(V("s"), Seq(V("t"), Plus, Call("omega", V("D"), V("i"))), V("p"))),
                "For every oscillator index i, multiplication by X(i) has two independent odd-frequency shifts "
                + "in the common kernel. The scalar products act by complex scalar multiplication. "
                + "Multiplying a bivariate polynomial by x^r or y^r shifts the corresponding convolution index by r."),
            Theorem("kernel-rectangular-support", "common_kernel_rectangular_support", "Separate lower bounds",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Polynomial, Comma, Sp,
                    Exists, Sp, Bound("u", Z), Comma, Sp, Bound("v", Z), Comma, Sp,
                    Forall, Sp, Indices, Comma, Sp, Open, V("s"), Lt, V("u"), Lor, Sp, V("t"), Lt, V("v"), Close,
                    Implies, K(V("s"), V("t"), V("p")), Eq, F.D(0)),
                "The finite support of pairTranslation(p) bounds its x and y exponents separately. "
                + "Take u and v to be the negatives of the two support suprema. Outside this rectangle "
                + "one creation index is negative in every summand, so the common kernel vanishes. "
                + "The zero polynomial and rank zero are included."),
            Theorem("kernel-ordered-support", "common_kernel_ordered_finite_support", "Finite support along both diagonals",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Indices, Comma, Sp, Polynomial, Comma, Sp,
                    Call("HasFiniteSupport", Call("lambda", Bound("d", N),
                        K(Seq(V("s"), Plus, V("d")), Seq(V("t"), Minus, V("d")), V("p")))), Land, Sp,
                    Call("HasFiniteSupport", Call("lambda", Bound("d", N),
                        K(Seq(V("s"), Minus, V("d")), Seq(V("t"), Plus, V("d")), V("p"))))),
                "For fixed s,t,p, both nonnegative-degree diagonal restrictions have finite support. "
                + "The forward bound comes from t-d<v, and the opposite bound from s-d<u. "
                + "Multiplying by contraction coefficients preserves this support and justifies every finsum distribution."),
            Paragraph(Text("Set kappa(D,a,b,d)=coeff_d(halfContraction D a b), where halfContraction is "
                + "rescale(-1,binomialSeries(B(a,b))) times binomialSeries(-B(a,b)), the expansion of "
                + "((1-z)/(1+z))^(B(a,b)). This is the original half-Fock contraction with both cover-pole factors. "
                + "Write A(a,s)=oscillatorCoefficient D a (s-q(a)).")),
            Theorem("native-ordered-product", "native_ordered_product", "Full forward composed-action identity",
                Seq(Forall, Sp, CommonParameters, Comma, Sp, Indices, Comma, Sp, Polynomial, Comma, Sp,
                    Call("A", V("D"), V("a"), V("s"), Call("A", V("D"), V("b"), V("t"), V("p"))),
                    Eq, Forward(V("p"))),
                "For all D,a,b,s,t,p without further hypotheses, A(a,s)(A(b,t)p) equals "
                + "the supported sum over d:N of kappa(D,a,b,d) times K(D,a,b,s+d,t-d,p). "
                + "For a constant polynomial, native half_creation_coefficient_transport evaluates each translated "
                + "creation coefficient exactly. Both the actual composite and the expansion are linear. "
                + "The existing native oscillatorCoefficient_X_mul identity gives the same two creator shifts as "
                + "kernel_creator. Structural induction on the full polynomial algebra therefore establishes the equality. "
                + "No product, locality, Jacobi or desired action identity is supplied as an assumption."),
            Paragraph(Text("The reverse ordered-product law, charged ground-product and tensor-product laws, "
                + "diagonal two-step locality, and the full native BPZ statement remain unproved here. "
                + "This forward oscillator identity alone does not establish a VOA, a full CFT, fusion or anomaly laws, "
                + "string dynamics, AdS/CFT, or a reconstruction of spacetime geometry."))
        )));
}
