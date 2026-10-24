// Narrative for the literal weighted fractional reciprocal transform.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class NymanWeightedFractionalInjectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.";
    private static Formula U => F.Id("u");
    private static Formula Y => F.Id("y");
    private static Formula W => F.Id("w");
    private static Formula R => F.Id("r");
    private static Formula G => F.Id("gamma");
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Positive => Seq(Open, D(0), Comma, Infty, Close);
    private static Formula Fract => Seq(Operatorname, Grp(F.Id("fract")), Open,
        Frac, Grp(D(1)), Grp(U, Y), Close);
    private static Formula Integrand => Seq(Apply(W, U), U, Caret,
        Grp(Minus, Half, Plus, F.Id("i"), G), Fract);
    private static Formula Transform => Seq(F.Id("H"), Underscore, Grp(G), W);
    private static Formula Actual => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(Infty),
        Integrand, Thin, F.Id("du"));
    private static Formula Weight => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(Infty),
        Norm(Apply(W, U)), U, Caret, Grp(R, Minus, D(1)), Thin, F.Id("du"), Lt, Infty);
    private static Formula Continuous => Seq(Operatorname, Grp(F.Id("ContinuousOn")),
        Open, W, Comma, Positive, Close);
    private static Formula Vanishes => Seq(Forall, Sp, Y, Gt, D(0), Comma,
        Apply(Transform, Y), Eq, D(0));
    private static Formula Zero => Seq(Forall, Sp, U, Gt, D(0), Comma,
        Apply(W, U), Eq, D(0));
    private static Formula Bind => Seq(Forall, Sp, W, Colon, Mathbb, Grp(F.Id("R")),
        To, Mathbb, Grp(F.Id("C")), Comma, Sp, R, Comma, G, InMacro, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted injectivity of the actual fractional reciprocal integral transform.",
        H("Weighted fractional-kernel injectivity"), Blocks(
            Paragraph(Text(""
                + "The literal coefficient "
                + "is fract(1/(u*y)); all powers of a positive real base use the principal complex power. "
                + "The parameter gamma is arbitrary and no hypothesis asserts that zeta vanishes.")),
            Describe.Lean(DescribeId.Create("weighted-fractional-integrand"),
                DeclarationHandle.Create(Prefix + "actualIntegrand"),
                H("Actual integrand"), StatementSource.FromAuthor(Disp(Integrand)),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The function of u is w(u)*u^(-1/2+i*gamma)*fract(1/(u*y)). "
                    + "The variables gamma and y are real; the injectivity theorem quantifies y>0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-fractional-transform"),
                DeclarationHandle.Create(Prefix + "actualTransform"),
                H("Actual integral transform"), StatementSource.FromAuthor(Disp(Seq(
                    Apply(Transform, Y), Eq, Actual))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the Bochner integral with respect to volume restricted "
                    + "to the positive half-line. The proof pays its absolute integrability for every "
                    + "positive y from the stated weighted domain; it does not use a total integral's "
                    + "undefined-value convention to bypass convergence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-fractional-domain"),
                DeclarationHandle.Create(Prefix + "WeightedIntegrable"),
                H("Absolute weighted domain"), StatementSource.FromAuthor(Disp(Weight)),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "WeightedIntegrable means IntegrableOn of the nonnegative real function "
                    + "norm(w(u))*u^(r-1) on (0,infinity). The continuity assumption in the theorem "
                    + "supplies measurability. No second weight is required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-fractional-injectivity"),
                DeclarationHandle.Create(Prefix + "weighted_fractional_transform_injective"),
                H("Injectivity on the weighted continuous domain"),
                StatementSource.FromAuthor(Disp(Seq(Bind, Minus, Half, Lt, R, Lt, Half, Land,
                    Continuous, Land, Weight, Land, Open, Vanishes, Close, Rightarrow, Zero))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Put kappa=1/2-r, f(v)=w(exp(v))*exp((r+i*gamma)*v), and "
                    + "k(z)=exp(-kappa*z)*fract(exp(z)). Then 0<kappa<1, f and k belong to L1, "
                    + "and norm(k(z))<=1 everywhere. The actual exp substitution, including the "
                    + "Jacobian exp(v), proves exp(-kappa*z)*H_gamma(w)(exp(-z))=(f*k)(z). "
                    + "The proof first establishes all actual integrals using f.mul_bdd. "
                    + "The already existing unit-interval Mellin identity plus the reciprocal tail "
                    + "gives mellin(fract(1/x),s)=-zeta(s)/s for 0<Re(s)<1. "
                    + "The tail's pointwise reduction calls the shared "
                    + "NymanFractionalMellin.fractionalMellin_tail_integrand_eq_cpow helper, "
                    + "extracted from the existing finite-tail proof; the extraction is source reuse "
                    + "and is not a new mathematical result. Applying the public "
                    + "mellin_eq_fourier theorem fixes Mathlib's 2*pi convention and gives "
                    + "Fourier(k)(xi)=-zeta(kappa+2*pi*i*xi)/(kappa+2*pi*i*xi). "
                    + "The public Fourier convolution theorem pays Fubini. The upstream discrete "
                    + "zeta zero set is countable, so the multiplier is nonzero on a dense subset "
                    + "of the frequency line. Continuity forces Fourier(f)=0 everywhere. The zero "
                    + "Fourier transform is integrable, so pointwise Fourier inversion at the "
                    + "continuous f gives f=0, and exp/log recovers w=0 on the positive half-line."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application to the original power class: let w be continuous on "
                + "(0,infinity), let a<1/2<b, let gamma be any real number, and suppose one "
                + "constant C bounds norm(w(u)) by C*u^(-a) for 0<u<=1 and by C*u^(-b) "
                + "for u>1. Choose max(a,-1/2)<r<1/2. The near-zero weighted majorant is "
                + "C*u^(r-a-1), and the tail majorant is C*u^(r-b-1), both integrable. "
                + "The weighted theorem therefore applies to this original class. Its exact "
                + "Lean application is supplied as a temporary example for scoped checking, without a retained "
                + "separate theorem, Describe entry or Reg wrapper. The private power-comparison "
                + "helper stays with that transient check and has no retained main-G consumer. "
                + "The input class and motivation are the paper-level fixed-profile obstruction "
                + "recorded in Library/Weil/baezduarte2000natural.md. This injectivity bridge "
                + "alone does not prove that obstruction's Order Lemma or interval-probe premises, "
                + "excludes no moving-profile or selected-subsequence construction, and establishes "
                + "no RH or signed Weil-energy conclusion."))), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin"))
        ]));
}
