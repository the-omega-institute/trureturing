using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class HighCosineThresholdLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest intermediate cosine level determines the high-threshold boundary for every modulus at least thirteen.",
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
                        + "the squared-distance bound for every feasible competitor and uniqueness. "
                        + "At a general real threshold s, PAt(q,s,x) uses tail mass (1−s)/(1−b(q)). "
                        + "The affine crossing gives a negative value at v(q) above the cutoff "
                        + "and a positive value below it.")),
                    Paragraph(Text(
                        "The slope for an intermediate level is the quadratic-multiplier slope "
                        + "plus nonnegative multiples of the reciprocals of its two distances from "
                        + "the outer cosine levels. The upper per-residue share p(q)/N(q) per unit of "
                        + "tail mass tends to one half, and the lower share (1−p(q))/M(q) tends to zero. "
                        + "For even moduli the lowest intermediate level is −u(q) and u(q)>8/9. "
                        + "For odd moduli the lower gap is at least 2 cos(π/q)(1−u(q)). "
                        + "These comparisons give strict dominance at v(q) from modulus thirteen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-contact-at-modulus-twelve"),
                DeclarationHandle.Create(Owner + ".cyclic_threshold_twelve_no_contact"),
                H("Sharpness at modulus twelve"),
                StatementSource.FromAuthor(Twelve()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus twelve the interval starts with a negative interpolant at v(12). "
                    + "The lowest intermediate level is −u, attained at residue five. Here u=√3/2, "
                    + "the lower level is −1 with multiplicity one, and g(u)(2u+1)=1 for "
                    + "g(x)=(1−x)(2x+1). The slope at −u is strictly greater than the slope "
                    + "at v(12), so v(12) has not reached zero at the exact cutoff."))),
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
        var cutoff = Call("a", q);
        var firstHeight = Call("PAt", q, one, contact);
        var s = F.Id("s");
        var crossing = Bind(FormulaQuantifier.ForAll, "s", R,
            Eq(Call("PAt", q, s, contact), Multiply(firstHeight,
                new Formula.Fraction(Subtract(s, cutoff), Subtract(one, cutoff)))));
        var domain = F.Seq(F.Forall, F.Sp, q, F.Sp, F.InMacro, F.Sp, N, F.Comma, F.Sp,
            new Formula.Relation(F.D(1, 3), FormulaRelationOperator.LessThanOrEqual, q),
            F.Sp, F.Longrightarrow, F.Sp, F.OpenBracket);
        return F.Disp(new Formula.Aligned([
            F.Seq(F.Amp, domain),
            F.Seq(F.Amp, Lt(lower, contact), F.Comma, F.Sp, Lt(contact, upper), F.Comma, F.Sp,
                attained, F.Comma, F.Sp, residual, F.Comma),
            F.Seq(F.Amp, multipliers, F.Comma, F.Sp, Eq(P(contact), zero), F.Comma, F.Sp, negative, F.Comma),
            F.Seq(F.Amp, nodeValues, F.Comma),
            F.Seq(F.Amp, expansion, F.Comma),
            F.Seq(F.Amp, positivePart, F.Comma, F.Sp, Call("Certified", q), F.Comma),
            F.Seq(F.Amp, Lt(cutoff, one), F.Comma, F.Sp, Lt(firstHeight, zero), F.Comma),
            F.Seq(F.Amp, crossing, F.CloseBracket)
        ]));
    }

    private static Formula Twelve()
    {
        var q = F.D(1, 2);
        return F.Disp(Lt(Call("P", q, Call("v", q)), F.D(0)));
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
