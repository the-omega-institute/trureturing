using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class HighCosineThresholdLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest intermediate cosine level determines the high-threshold boundary for large cycles.",
        H("First contact at the high-threshold boundary"),
        Blocks(
            Paragraph(Text(
                "For modulus q let c(q,i) = cos(2πi/q), with u(q) = c(q,1), "
                + "l(q) = c(q,⌊q/2⌋) and v(q) = cos(4π/q). Let a(q) be the exact high-threshold "
                + "cutoff from the finite three-level certificate, and b(q) the common tail moment. "
                + "Use r(q) = (1−a(q))/(1−b(q)), the upper tail fraction p(q), and counts "
                + "N(q), M(q) at u(q), l(q) respectively. The law w(q,i) has weights determined "
                + "by r(q), p(q) and these counts.")),
            Describe.Lean(
                DescribeId.Create("first-intermediate-cosine-contact"),
                DeclarationHandle.Create(Owner + ".cyclic_threshold_first_contact"),
                H("The first intermediate contact and the strictly positive multipliers"),
                StatementSource.FromAuthor(FirstContact()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "P(q,x) denotes the quadratic interpolant at the cutoff and A(q), B(q), "
                        + "G(q) are its coefficients in the basis 1, x, 2x²−1. "
                        + "With Lagrange coefficients T, U, L at the three nodes, "
                        + "A(q) = T u(q) l(q) + U l(q) + L u(q) + G(q). "
                        + "Certified(q) is the finite certificate at a(q), including normalized "
                        + "nonnegative weights, both moments equal to a(q), the exact squared mass, "
                        + "the squared-distance bound for every feasible competitor and uniqueness.")),
                    Paragraph(Text(
                        "The slope for an intermediate level is the quadratic-multiplier slope "
                        + "plus nonnegative multiples of the reciprocals of its two distances from "
                        + "the outer cosine levels. The lower distance is at least 1−u(q) for either parity. "
                        + "The upper per-residue mass tends to one half and the lower per-residue mass tends to zero. "
                        + "The two reciprocal terms then give a strict comparison in favor of v(q), "
                        + "uniform over all the other intermediate levels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-cosine-threshold-limit"),
                DeclarationHandle.Create(Owner + ".cyclic_criticalThreshold_limit"),
                H("The sharp asymptotic width of the high-threshold interval"),
                StatementSource.FromAuthor(CutoffLimit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "As q tends to infinity, the winning slope tends to 5/3. "
                    + "After division by 1−u(q), the tail-moment deficit tends to 4. "
                    + "The half-angle identity and the sine quotient limit give "
                    + "q²(1−u(q)) tending to 2π². Together these determine the limit."))),
                DescribeRole.Theorem))));

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) =>
        new Formula.BindMany(quantifier,
            [new Formula.BoundVariable(FormulaIdentifier.Create(variable), domain)], body);

    private static Formula FirstContact()
    {
        var q = F.Id("q");
        var threshold = F.Id("Q");
        var i = F.Id("i");
        var x = F.Id("x");
        var upper = Call("u", q);
        var lower = Call("l", q);
        var contact = Call("v", q);
        var c = Call("c", q, i);
        var r = Call("r", q);
        var p = Call("p", q);
        var beta = Call("B", q);
        var gamma = Call("G", q);
        var indices = Call("Fin", q);
        var one = F.D(1);
        var zero = F.D(0);
        Formula P(Formula level) => Call("P", q, level);
        var differentIntermediate = And(Lt(lower, c), And(Lt(c, upper),
            new Formula.Relation(c, FormulaRelationOperator.NotEqual, contact)));
        var attained = Bind(FormulaQuantifier.Exists, "i", indices, Eq(c, contact));
        var residual = And(Lt(zero, r), Lt(r, one));
        var multipliers = And(Lt(zero, beta), Lt(zero, gamma));
        var negative = Bind(FormulaQuantifier.ForAll, "i", indices,
            Imp(differentIntermediate, Lt(P(c), zero)));
        var nodeValues = And(Eq(P(one), Subtract(one, r)),
            And(Eq(P(upper), new Formula.Fraction(Multiply(r, p), Call("N", q))),
                Eq(P(lower), new Formula.Fraction(Multiply(r, Subtract(one, p)), Call("M", q)))));
        var second = Subtract(Multiply(F.D(2), new Formula.Power(x, F.D(2))), one);
        var expansion = Bind(FormulaQuantifier.ForAll, "x", R,
            Eq(P(x), Add(Add(Call("A", q), Multiply(beta, x)), Multiply(gamma, second))));
        var positivePart = Bind(FormulaQuantifier.ForAll, "i", indices,
            Eq(Call("w", q, i), Call("max", zero, P(c))));
        var domain = F.Seq(F.Exists, F.Sp, threshold, F.Sp, F.InMacro, F.Sp, N,
            F.Comma, F.Sp, F.Forall, F.Sp, q, F.Sp, F.InMacro, F.Sp, N, F.Comma, F.Sp,
            new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, q),
            F.Sp, F.Longrightarrow, F.Sp, F.OpenBracket);
        return F.Disp(new Formula.Aligned([
            F.Seq(F.Amp, domain),
            F.Seq(F.Amp, Lt(lower, contact), F.Comma, F.Sp, Lt(contact, upper), F.Comma, F.Sp,
                attained, F.Comma, F.Sp, residual, F.Comma),
            F.Seq(F.Amp, multipliers, F.Comma, F.Sp, Eq(P(contact), zero), F.Comma, F.Sp, negative, F.Comma),
            F.Seq(F.Amp, nodeValues, F.Comma),
            F.Seq(F.Amp, expansion, F.Comma),
            F.Seq(F.Amp, positivePart, F.Comma, F.Sp, Call("Certified", q), F.CloseBracket)
        ]));
    }

    private static Formula CutoffLimit()
    {
        var q = F.Id("q");
        var numerator = Multiply(F.D(2, 4), new Formula.Power(F.Pi, F.D(2)));
        var value = Multiply(new Formula.Power(q, F.D(2)), Subtract(F.D(1), Call("a", q)));
        var sequence = F.Seq(F.Open, q, F.Colon, N, F.Mapsto, F.Sp, value, F.Close);
        return F.Disp(Call("TendstoAtTop", sequence, new Formula.Fraction(numerator, F.D(5))));
    }
}
