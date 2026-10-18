using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinElasticityMonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real-power certificate makes the binary Renyi elasticity transform monotone for every real n at least one.",
        H("Real-Power Elasticity Monotonicity"),
        Blocks(
            Paragraph(Text("The parameter n is real. The monotonicity domain is the open interval (0,1), "
                + "and n = 1 is included. Powers with the exponents n, n minus one and twice n use Real.rpow; "
                + "the displayed square factors use natural exponent two. The definitions are total real functions, "
                + "while the sign and derivative arguments below use strictly positive bases.")),
            Node("T", "Power-ratio transform", AllReal("n", AllReal("r",
                Equal(Call("T", N("n"), N("r")), TBody()))), DescribeRole.Definition,
                "T compares the difference and sum of one and the nth power of r."),
            Node("A", "Logarithmic derivative factor", AllReal("n", AllReal("r",
                Equal(Call("A", N("n"), N("r")), ABody()))), DescribeRole.Definition,
                "This factor will equal t times the logarithmic derivative of T(n,(1-t)/(1+t))."),
            Node("B", "Bias-times-transform factor", AllReal("n", AllReal("r",
                Equal(Call("B", N("n"), N("r")), BBody()))), DescribeRole.Definition,
                "The bias coordinate corresponding to r is (1-r)/(1+r)."),
            Node("F", "Elasticity transform", AllReal("n", AllReal("r",
                Equal(Call("F", N("n"), N("r")), new Formula.Fraction(
                    Subtract(Call("A", N("n"), N("r")), Call("B", N("n"), N("r"))),
                    Add(D(1), Call("B", N("n"), N("r"))))))), DescribeRole.Definition,
                "F is the real-power expression for the elasticity of minus the derivative of binary Renyi entropy in bias coordinates."),
            Node("J", "Real-power sign certificate", AllReal("n", AllReal("z", JFormula())),
                DescribeRole.Definition, "The four-term auxiliary function controls the sign of A's derivative."),
            Node("J₁", "First derivative certificate", AllReal("n", AllReal("z",
                Equal(Call("J₁", N("n"), N("z")), Multiply(Add(N("n"), D(1)),
                    Subtract(Add(Negative(D(1)), Multiply(N("n"), Pow(N("z"), Subtract(N("n"), D(1))))),
                        Multiply(Subtract(N("n"), D(1)), Pow(N("z"), N("n")))))))),
                DescribeRole.Definition, "J₁ records the derivative of J on positive bases."),
            Node("J_hasDerivAt", "Derivative of J", AllReal("n", AllReal("z",
                Imp(Rel(D(0), FormulaRelationOperator.LessThan, N("z")),
                    Call("HasDerivAt", Call("J", N("n")), Call("J₁", N("n"), N("z")), N("z"))))),
                DescribeRole.Theorem, "The real-power derivative identity requires only a positive base."),
            Node("J₁_hasDerivAt", "Second derivative of J", AllReal("n", AllReal("z",
                Imp(Rel(D(0), FormulaRelationOperator.LessThan, N("z")),
                    Call("HasDerivAt", Call("J₁", N("n")),
                        Multiply(Multiply(Multiply(N("n"), Subtract(Pow(N("n"), D(2)), D(1))),
                            Pow(N("z"), Subtract(N("n"), D(2)))), Subtract(D(1), N("z"))), N("z"))))),
                DescribeRole.Theorem, "The second derivative factors into a parameter sign and positive-base factors."),
            Node("J_nonneg", "Nonnegativity of J from its curvature", AllReal("n", AllReal("z",
                Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual,
                    Multiply(N("n"), Subtract(Pow(N("n"), D(2)), D(1)))),
                    Imp(Rel(N("z"), FormulaRelationOperator.MemberOf, Interval("Ioo", D(0), D(1))),
                        Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("J", N("n"), N("z"))))))),
                DescribeRole.Theorem, "J and its first derivative vanish at one. Nonnegative second derivative "
                    + "therefore gives J >= 0. The condition includes both n >= 1 and -1 < n < 0."),
            Node("A₁", "Derivative expression for A", AllReal("n", AllReal("r",
                Equal(Call("A₁", N("n"), N("r")), new Formula.Fraction(
                    Multiply(Multiply(N("n"), Pow(N("r"), Subtract(N("n"), D(2)))),
                        Call("J", N("n"), Pow(N("r"), D(2)))),
                    Pow(Subtract(D(1), Pow(N("r"), Multiply(D(2), N("n")))), D(2)))))),
                DescribeRole.Definition, "This is the explicit real-power derivative of A."),
            Node("B₁", "Derivative expression for B", AllReal("n", AllReal("r",
                Equal(Call("B₁", N("n"), N("r")),
                    Subtract(new Formula.Fraction(Multiply(Negative(D(2)), Call("T", N("n"), N("r"))),
                        Pow(Add(D(1), N("r")), D(2))),
                        new Formula.Fraction(Multiply(Multiply(Multiply(D(2), N("n")),
                            new Formula.Fraction(Subtract(D(1), N("r")), Add(D(1), N("r")))),
                            Pow(N("r"), Subtract(N("n"), D(1)))),
                            Pow(Add(D(1), Pow(N("r"), N("n"))), D(2))))))),
                DescribeRole.Definition, "The two-term derivative of B is shared by both order regimes."),
            Node("F₁", "Derivative expression for F", AllReal("n", AllReal("r",
                Equal(Call("F₁", N("n"), N("r")), Subtract(
                    new Formula.Fraction(Call("A₁", N("n"), N("r")), Add(D(1), Call("B", N("n"), N("r")))),
                    new Formula.Fraction(Multiply(Add(D(1), Call("A", N("n"), N("r"))), Call("B₁", N("n"), N("r"))),
                        Pow(Add(D(1), Call("B", N("n"), N("r"))), D(2))))))),
                DescribeRole.Definition, "This expression separates the two derivative signs needed by the elasticity certificate."),
            Node("A_hasDerivAt", "Derivative of A for nonzero real n", DerivativeDomain("A", "A₁", false),
                DescribeRole.Theorem, "The denominator is nonzero for every nonzero n and 0 < r < 1. "
                    + "Both positive and negative real parameters use the same derivative proof."),
            Node("B_hasDerivAt", "Derivative of B", AllReal("n", AllReal("r",
                Imp(Rel(N("r"), FormulaRelationOperator.MemberOf, Interval("Ioo", D(0), D(1))),
                    Call("HasDerivAt", Call("B", N("n")), Call("B₁", N("n"), N("r")), N("r"))))),
                DescribeRole.Theorem, "The power-ratio derivative and product rule apply to every real n."),
            Node("F_hasDerivAt", "Derivative of F", DerivativeDomain("F", "F₁", true),
                DescribeRole.Theorem, "The quotient rule applies when n is nonzero and 1+B is positive. "
                    + "The positive- and negative-order consumers establish that sign separately."),
            Node("T_pos", "Positivity of the power-ratio transform", WithDomain(
                Rel(D(0), FormulaRelationOperator.LessThan, Call("T", N("n"), N("r")))),
                DescribeRole.Theorem,
                "For n at least one and 0 < r < 1, the nth power of r lies strictly between zero and one. "
                + "Thus the numerator and denominator of T are both positive."),
            Node("T_hasDerivAt", "Derivative of the power-ratio transform", AllReal("n", AllReal("r",
                Imp(Rel(D(0), FormulaRelationOperator.LessThan, N("r")),
                    Call("HasDerivAt", Call("T", N("n")), new Formula.Fraction(
                        Multiply(Multiply(Negative(D(2)), N("n")), Pow(N("r"), Subtract(N("n"), D(1)))),
                        Pow(Add(D(1), Pow(N("r"), N("n"))), D(2))), N("r"))))),
                DescribeRole.Theorem,
                "Only r > 0 is required; n is any real number. The proof directly uses Mathlib's real-power derivative and the quotient rule."),
            Node("A_eq", "Factoring the denominator of A", AllReal("n", AllReal("r",
                Imp(Rel(D(0), FormulaRelationOperator.LessThan, N("r")),
                    Equal(Call("A", N("n"), N("r")), new Formula.Fraction(ANumerator(),
                        Multiply(Subtract(D(1), Pow(N("r"), N("n"))),
                            Add(D(1), Pow(N("r"), N("n"))))))))), DescribeRole.Theorem,
                "For a positive base, the real-power product law identifies r to twice n with the square of r to n. "
                + "Factoring the difference of squares gives this identity without a restriction on n."),
            Node("monotoneOn_F", "Monotonicity of the elasticity transform", AllReal("n",
                Imp(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, N("n")),
                    Call("MonotoneOn", Call("F", N("n")), Interval("Ioo", D(0), D(1))))),
                DescribeRole.Theorem,
                "For every real n at least one, F(n,r) is nondecreasing on (0,1). "
                + "The proof in fact establishes a strictly positive derivative on that interval."),
            Paragraph(Text("The sign certificate is the four-term real-power function "), Math(JFormula()),
                Text(". Its first derivative is (n+1)(-1+n z^(n-1)-(n-1)z^n), and its second derivative is "
                    + "n(n^2-1) z^(n-2)(1-z). The second derivative is nonnegative on (0,1). "
                    + "On each interval [z,1] with z > 0, derivative monotonicity and J'(1)=J(1)=0 first give J' <= 0 and then J >= 0. "
                    + "No differentiability at zero is needed when 1 <= n < 2.")),
            Paragraph(Text("Differentiating A gives A'(r)=n r^(n-2) J(r^2)/(1-r^(2n))^2, hence A' >= 0. "
                + "The derivative of B is -2 T/(1+r)^2 - 2n((1-r)/(1+r))r^(n-1)/(1+r^n)^2, which is strictly negative. "
                + "Since A and B are positive, F'=A'/(1+B)-(1+A)B'/(1+B)^2 is strictly positive. "
                + "At n=1 the J term vanishes, but the B term remains strictly negative.")),
            Paragraph(Text("The consumer is the alpha-at-least-two clause of C. Hirche, Renyi Bounds on Information Combining, "
                + "ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18. This certificate supplies the real-order "
                + "one-variable inequality; it does not assert a result for orders below two.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-elasticity-" + name.ToLowerInvariant().Replace('_', '-').Replace("₁", "1")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula N(string value) => F.Id(value);
    private static Formula RealType() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula AllReal(string name, Formula body) =>
        Seq(Forall, Sp, Par(Seq(N(name), Colon, Sp, RealType())), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, conclusion);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Par(value), exponent);
    private static Formula Negative(Formula value) => Seq(Minus, value);
    private static Formula Interval(string name, Formula left, Formula right) => Call(name, left, right);
    private static Formula WithDomain(Formula body) => AllReal("n", AllReal("r",
        Imp(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, N("n")),
            Imp(Rel(N("r"), FormulaRelationOperator.MemberOf, Interval("Ioo", D(0), D(1))), body))));
    private static Formula DerivativeDomain(string function, string derivative, bool denominator) {
        Formula conclusion = Call("HasDerivAt", Call(function, N("n")), Call(derivative, N("n"), N("r")), N("r"));
        if (denominator) conclusion = Imp(Rel(D(0), FormulaRelationOperator.LessThan,
            Add(D(1), Call("B", N("n"), N("r")))), conclusion);
        return AllReal("n", AllReal("r", Imp(Rel(N("n"), FormulaRelationOperator.NotEqual, D(0)),
            Imp(Rel(N("r"), FormulaRelationOperator.MemberOf, Interval("Ioo", D(0), D(1))), conclusion))));
    }
    private static Formula TBody() => new Formula.Fraction(Subtract(D(1), Pow(N("r"), N("n"))),
        Add(D(1), Pow(N("r"), N("n"))));
    private static Formula ANumerator() => Multiply(Multiply(N("n"), Pow(N("r"), Subtract(N("n"), D(1)))),
        Subtract(D(1), Pow(N("r"), D(2))));
    private static Formula ABody() => new Formula.Fraction(ANumerator(),
        Subtract(D(1), Pow(N("r"), Multiply(D(2), N("n")))));
    private static Formula BBody() => Multiply(new Formula.Fraction(Subtract(D(1), N("r")), Add(D(1), N("r"))),
        Call("T", N("n"), N("r")));
    private static Formula JFormula() => Equal(Call("J", N("n"), N("z")),
        Subtract(Add(Subtract(Subtract(N("n"), D(1)), Multiply(Add(N("n"), D(1)), N("z"))),
            Multiply(Add(N("n"), D(1)), Pow(N("z"), N("n")))),
            Multiply(Subtract(N("n"), D(1)), Pow(N("z"), Add(N("n"), D(1))))));
}
