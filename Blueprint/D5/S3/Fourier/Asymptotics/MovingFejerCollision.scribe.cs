using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class MovingFejerCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/MovingFejerCollision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible variance and resolution window yields a collision lower bound with a threshold independent of the frequency family.",
        H("Uniform collision lower bound at moving resolution"),
        Blocks(
            Paragraph(Text(
                "Let V(n) and eta(n) be real sequences indexed by natural n, both eventually positive. " +
                "Write s(n)=sqrt(n V(n)) and r(n)=eta(n)/s(n).")),
            Describe.Lean(DescribeId.Create("compatible-window"),
                DeclarationHandle.Create(Owner + ".exists_fejer_window_iff"),
                H("Compatibility of the two window scales"),
                StatementSource.FromAuthor(Compatibility()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If r(n) tends to zero, choose A(n)=1/(s(n)sqrt(r(n))). Eventually all factors " +
                    "are positive. The normalized radius A(n)s(n) equals 1/sqrt(r(n)) and tends to " +
                    "positive infinity. The resolution-scaled radius eta(n)A(n) equals sqrt(r(n)) " +
                    "and tends to zero. Conversely, for any such eventually positive A(n), " +
                    "r(n)=(eta(n)A(n))/(s(n)A(n)) eventually, whose limit is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-lower"),
                DeclarationHandle.Create(Owner + ".moving_fejer_uniform_lower"),
                H("Uniform Gaussian lower coefficient"),
                StatementSource.FromAuthor(Lower()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume r(n) tends to zero. For each epsilon>0, the degree threshold comes before " +
                        "the choice of finite index type J, real frequencies g(j), nonnegative weights w(j), " +
                        "or real center a. Let W be the sum of the weights, E(n) the ordered-pair collision " +
                        "mass of degree-n frequency sums at the closed resolution eta(n), and assume " +
                        "sum_j w(j)(g(j)-a)^2 <= V(n) W. All such data beyond the threshold satisfy the bound.")),
                    Paragraph(Text(
                        "Take the compatible window A(n) and set c=1/(2 pi)-epsilon/(2 sqrt(pi)). " +
                        "The normalized angular Fejer kernel equals (1/(2 pi)) sinc(eta(n)t/2)^2. " +
                        "It is at least c throughout the window eventually, since eta(n)A(n) tends to zero " +
                        "and sinc is continuous at zero. The scaled unweighted clipped integral over this " +
                        "window tends to sqrt(pi) because A(n)s(n) tends to infinity. Thus its product with c " +
                        "tends to 1/(2 sqrt(pi))-epsilon/2. Apply the finite-window collision inequality " +
                        "with the same n and budget. This argument gives a threshold depending only on the " +
                        "two sequences and epsilon, allowing the frequency family and its cardinality to vary.")),
                    Paragraph(Text(
                        "For example, with positive total weight the bound yields a liminf of at least " +
                        "1/(2 sqrt(pi)) for s(n)E(n)/(eta(n)W^(2n)). The small-resolution hypothesis " +
                        "is essential to this argument: even a single unit-weight frequency with " +
                        "V(n)=1/n² and fixed positive eta has scaled collision ratio tending to zero. " +
                        "Uniform upper bounds for high-degree collisions of actual zeta ordinates remain open."))),
                DescribeRole.Theorem))));

    private static Formula N => F.Id("n");
    private static Formula AtInfinity(Formula body) =>
        F.Seq(F.Lim, F.Underscore, F.Grp(N, F.Sp, F.To, F.Sp, F.Infty), F.Sp, body);
    private static Formula Compatibility()
    {
        Formula a = Call("A", N);
        Formula s = Call("s", N);
        Formula eta = Call("eta", N);
        Formula exists = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("A"),
                new Formula.Power(F.Seq(F.Mathbb,F.Grp(F.Id("R"))), F.Seq(F.Mathbb,F.Grp(F.Id("N")))))],
            new Formula.Logic(Call("EventuallyPositive", F.Id("A")), FormulaLogicOperator.And,
                new Formula.Logic(Equal(AtInfinity(Multiply(a,s)), F.Infty), FormulaLogicOperator.And,
                    Equal(AtInfinity(Multiply(eta,a)), F.D(0)))));
        return F.Disp(new Formula.Logic(Equal(AtInfinity(Call("r",N)), F.D(0)),
            FormulaLogicOperator.Iff, exists));
    }

    private static Formula Lower()
    {
        Formula coefficient = Subtract(new Formula.Fraction(F.D(1),
            Multiply(F.D(2), F.Seq(F.Sqrt, F.Grp(F.Pi)))), F.Varepsilon);
        Formula left = Multiply(Multiply(coefficient, Call("eta",N)),
            new Formula.Power(F.Id("W"), Multiply(F.D(2), N)));
        Formula right = Multiply(Call("s",N), Call("E",N));
        return F.Disp(new Formula.Logic(Equal(AtInfinity(Call("r",N)), F.D(0)),
            FormulaLogicOperator.Implies,
            F.Seq(F.Forall, F.Sp, F.Varepsilon, F.Sp, F.Gt, F.Sp, F.D(0),
                F.Comma, F.Sp, Call("EventuallyForAllData",
                    new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right)))));
    }
}
