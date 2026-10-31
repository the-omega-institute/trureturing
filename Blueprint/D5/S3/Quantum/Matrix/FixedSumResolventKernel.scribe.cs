using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class FixedSumResolventKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/FixedSumResolventKernel.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));
    private static Formula R(Formula s, Formula r, Formula x) => Call("R", s, r, x);
    private static Formula K(Formula s, Formula j, Formula r) => Call("K", s, j, r);
    private static Formula Moment(Formula j, Formula a, Formula b) => Call("M", j, a, b);
    private static Formula AllReals(Formula names, Formula body) => Seq(
        Forall, Sp, names, Sp, InMacro, Sp, Mathbb, Grp(V("R")), Comma, Quad, body);
    private static Formula Integral(Formula x, Formula body) => Seq(Int, Underscore,
        Grp(x, Gt, D(0)), Sp, body, Sp, Mathrm, Grp(V("d")), Sp, x);
    private static Formula Pow(Formula x, Formula j) => new Formula.Power(x, j);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-sum resolvent moments are convex, and weighted Jensen bounds arbitrary finite spectral sums.",
        H("Fixed-sum scalar resolvent convexity"), Blocks(
            Entry("resolvent", "fixed-sum-resolvent", "Scalar shifted response product",
                AllReals(Seq(V("S"), Comma, V("r"), Comma, V("s")), Seq(
                    R(V("S"), V("r"), V("s")), Eq,
                    Fr(Sq(V("r")), Seq(Sq(V("s")), Plus, V("S"), V("s"), Plus, Sq(V("r")))))),
                "R(S,r,s)=r²/(s²+Ss+r²) uses the total real division operation. The integrals only use s>0. When S>0 its denominator is strictly positive there, including r=0.", true),
            Entry("kernel", "fixed-sum-kernel", "Integrated fixed-sum moment",
                AllReals(Seq(V("S"), Comma, V("r")), Seq(
                    Forall, Sp, V("j"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Quad,
                    K(V("S"), V("j"), V("r")), Eq,
                    Fr(Integral(V("s"), Pow(R(V("S"), V("r"), V("s")), V("j"))), V("j")))),
                "K(S,j,r) is 1/j times the Lebesgue integral on the positive half-line. All analytic claims require the positive integer order j≥1; the definition itself is total.", true),
            Describe.Lean(DescribeId.Create("fixed-sum-kernel-integrability"),
                DeclarationHandle.Create(Prefix + "integrable_resolvent"), H("Derived integrability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real S>0, every real r, and every natural j≥1, the function s↦R(S,r,s)^j is integrable on s>0. It lies between zero and (r²+1)/(1+s²). This domination treats both the origin and the infinite tail and includes r=0."))), DescribeRole.Theorem),
            Entry("convex_kernel", "fixed-sum-kernel-convexity", "Convexity on the closed half-line",
                AllReals(V("S"), Seq(
                    Forall, Sp, V("j"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Quad,
                    V("S"), Gt, D(0), Sp, Land, Sp, V("j"), Ge, D(1), Sp, Rightarrow, Sp,
                    Call("ConvexOn", MathbbReal(), Call("Ici", D(0)), Call("K", V("S"), V("j"))))),
                "For every S>0 and every positive integer j, K(S,j,·) is convex on the entire closed nonnegative half-line. Layer cake writes K as the integral over 0<t<1 of t^(j−1)L(S,r,t), where L=(sqrt(S²+4r²(t⁻¹−1))−S)/2. The superlevel interval is proved by solving the quadratic inequality. The square root is the complex-plane Euclidean norm of (S,2sqrt(t⁻¹−1)r); its triangle inequality proves convexity. Tonelli and the already derived finite resolvent integral also prove integrability of the layer density. Thus neither differentiation under an improper integral nor assumed endpoint continuity is used.", false),
            Entry("scalarMoment", "scalar-resolvent-moment", "Two-eigenvalue moment",
                AllReals(Seq(V("u"), Comma, V("v")), Seq(
                    Forall, Sp, V("j"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Quad,
                    Moment(V("j"), V("u"), V("v")), Eq,
                    Fr(Integral(V("s"), Pow(Fr(Seq(V("u"), V("v")),
                        Seq(Open, V("s"), Plus, V("u"), Close, Open, V("s"), Plus, V("v"), Close)), V("j"))), V("j")))),
                "For nonnegative u,v this is K(u+v,j,sqrt(uv)). Either zero input gives zero at every positive integer order.", true),
            Describe.Lean(DescribeId.Create("scalar-resolvent-moment-integrability"),
                DeclarationHandle.Create(Prefix + "integrable_scalar"), H("Zero-safe scalar integrability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all nonnegative real u,v and all natural j≥1, s↦[uv/((s+u)(s+v))]^j is integrable on s>0. If u+v>0 this follows from the fixed-sum integrability theorem. If u+v=0, nonnegativity forces u=v=0 and the integrand vanishes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-spectral-fidelity-moment"),
                DeclarationHandle.Create(Prefix + "scalar_fidelity_moment"), H("Arbitrary finite spectral bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite type I and a,b:I→ℝ with a_i,b_i≥0, α=Σ_i a_i>0, β=Σ_i b_i>0, T=Σ_i sqrt(a_i b_i), and any natural j≥1, M(j,α,β)[T²/(αβ)]^j≤Σ_i M(j,a_i,b_i). No equality of the two traces or positivity of individual eigenvalues is assumed.")),
                    Paragraph(Text("Put S=α+β, w_i=(a_i+b_i)/S, and r_i=sqrt(a_i b_i)/w_i, with total division at zero. Zero w_i forces a_i=b_i=0. Positive homogeneity gives M(j,a_i,b_i)=w_i K(S,j,r_i); the weights sum to one and Σ_i w_i r_i=T. Weighted convex Jensen gives K(S,j,T)≤Σ_i M(j,a_i,b_i). Cauchy–Schwarz gives T²≤αβ. Comparing the positive denominators pointwise gives [T²/(αβ)]^j K(S,j,sqrt(αβ))≤K(S,j,T). This is a weighted Jensen argument and makes no reversed unweighted power-sum claim."))),
                DescribeRole.Theorem))));

    private static Formula MathbbReal() => Seq(Mathbb, Grp(V("R")));
    private static DocumentBlock Entry(string name, string id, string heading, Formula formula,
        string text, bool definition) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
