using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FejerCollisionVarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FejerCollisionVariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive angular Fejer kernel retains a closed collision band for arbitrary real frequency sums.",
        H("Real-frequency collision variance bound"),
        Blocks(
            Paragraph(Text(
                "Fix a finite index set J, real frequencies g(j), real weights w(j), and a positive " +
                "resolution eta. Let S(t)=sum_j w(j) exp(i g(j)t), W=sum_j w(j). For natural degree p, " +
                "the index family consists of the nonnegative integer multiplicity vectors of total degree p. " +
                "Write G(m) for their frequency sums and c(m) for their multinomial weights. " +
                "E(p) is the sum of c(m)c(n) over the ordered pairs with |G(m)-G(n)|<=eta. " +
                "Set K(t)=eta/(2 pi) sinc(eta t/2)^2 and phi(d)=max(0,1-|d|/eta). " +
                "Write M(p) for the whole-line integral of K(t)|S(t)|^(2p) and T(p) for the finite " +
                "double sum of c(m)c(n)phi(G(m)-G(n)).")),
            Describe.Lean(DescribeId.Create("triangular-band"),
                DeclarationHandle.Create(Owner + ".fejer_collision_comparison"),
                H("Exact triangular-band comparison"),
                StatementSource.FromAuthor(Comparison()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all signed weights the exact finite pair expansion of the even score power " +
                    "and integration of each cosine against K give M(p)=T(p). The existing angular Fejer " +
                    "law supplies the integrability, nonnegativity and exact triangular Fourier transform. " +
                    "If the input weights are nonnegative, every multinomial pair weight is nonnegative, " +
                    "and phi(d) is bounded by the indicator of |d|<=eta. The comparison includes the " +
                    "closed band boundary, where phi is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-window"),
                DeclarationHandle.Create(Owner + ".fejer_collision_variance_lower"),
                H("Retained finite-window contribution"),
                StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative weights assume sum_j w(j)(g(j)-a)^2<=V W around an arbitrary " +
                    "real center a and with real budget V. For each A>=0 let I(p,A) denote the integral " +
                    "of K(t) max(0,1-Vt^2/2)^(2p) from -A to A. The pointwise score variance " +
                    "minorant gives the claimed bound inside the window. The positive kernel allows " +
                    "this integral to be bounded by the full-line weighted score moment, which is " +
                    "already controlled by E(p). There is no lattice restriction on the frequencies."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("asymptotic-coefficient"),
                DeclarationHandle.Create(Owner + ".fejer_collision_asymptotic_lower"),
                H("Gaussian lower coefficient at fixed positive resolution"),
                StatementSource.FromAuthor(Asymptotic()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In addition assume V>0 and keep all data, V and eta fixed while p tends to infinity. " +
                    "For each epsilon>0, put c=eta/(2 pi)-epsilon/(2 sqrt(pi)). Since K(0)=eta/(2 pi) " +
                    "and K is continuous, there is a fixed positive A such that K(t)>=c for |t|<=A. " +
                    "The scaled unweighted clipped power integral on this window tends to sqrt(pi). " +
                    "Consequently its product with c tends to eta/(2 sqrt(pi))-epsilon/2. " +
                    "For all sufficiently large p it exceeds the required coefficient. Apply the finite-window " +
                    "bound with the same variance and weights. The result is a lower bound for arbitrary " +
                    "real frequency families, including finite zeta tails. Uniformity for growing families " +
                    "or changing eta and V, and upper bounds for actual high-degree collisions, require " +
                    "further estimates."))),
                DescribeRole.Theorem))));

    private static Formula P => F.Id("p");
    private static Formula E => Call("E", P);
    private static Formula WeightPower => new Formula.Power(F.Id("W"), Multiply(F.D(2), P));
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Comparison() =>
        F.Disp(new Formula.Logic(Equal(Call("M", P), Call("T", P)), FormulaLogicOperator.And,
            new Formula.Logic(Call("Nonnegative", F.Id("w")), FormulaLogicOperator.Implies,
                Le(Call("M", P), E))));

    private static Formula Window() =>
        F.Disp(Le(Multiply(WeightPower, Call("I", P, F.Id("A"))), E));

    private static Formula Asymptotic()
    {
        Formula coefficient = Subtract(new Formula.Fraction(F.Id("eta"),
            Multiply(F.D(2), F.Seq(F.Sqrt, F.Grp(F.Pi)))), F.Varepsilon);
        Formula right = Multiply(F.Seq(F.Sqrt, F.Grp(Multiply(P, F.Id("V")))), E);
        return F.Disp(F.Seq(F.Forall, F.Sp, F.Varepsilon, F.Sp, F.Gt, F.Sp, F.D(0), F.Comma, F.Sp,
            Call("Eventually", Le(Multiply(coefficient, WeightPower), right))));
    }
}
