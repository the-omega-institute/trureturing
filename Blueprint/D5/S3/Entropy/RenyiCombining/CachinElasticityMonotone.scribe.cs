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
            Paragraph(Text("The derivative certificate is J₁(n,z)=(n+1)(-1+n z^(n-1)-(n-1)z^n). "
                + "It records the first derivative of J on positive bases.")),
            Paragraph(Text("The explicit derivative expressions are A₁(n,r)=n r^(n-2) J(n,r^2)/(1-r^(2n))^2, "
                + "B₁(n,r)=-2 T(n,r)/(1+r)^2-2n((1-r)/(1+r))r^(n-1)/(1+r^n)^2, "
                + "and F₁(n,r)=A₁(n,r)/(1+B(n,r))-(1+A(n,r))B₁(n,r)/(1+B(n,r))^2. "
                + "These functions separate the derivative signs used in the positive and negative order regimes.")),
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
            Node("antitoneOn_F_neg", "Antitonicity at negative parameters",
                AllReal("n", Imp(Seq(Rel(Negative(D(1)), FormulaRelationOperator.LessThan, N("n")),
                    Sp, Land, Sp, Rel(N("n"), FormulaRelationOperator.LessThan, D(0))),
                    Call("AntitoneOn", Call("F", N("n")), Interval("Ioo", D(0), D(1))))),
                DescribeRole.Theorem,
                "For -1 < n < 0, J remains nonnegative and the factor n reverses A's derivative sign. "
                    + "Here A > 0, -1 < B < 0 and B' > 0, so F' < 0. This supplies the orders below one."),
            Paragraph(Text("The sign certificate is the four-term real-power function "), Math(JFormula()),
                Text(". Its first derivative is (n+1)(-1+n z^(n-1)-(n-1)z^n), and its second derivative is "
                    + "n(n^2-1) z^(n-2)(1-z). The second derivative is nonnegative on (0,1). "
                    + "On each interval [z,1] with z > 0, derivative monotonicity and J'(1)=J(1)=0 first give J' <= 0 and then J >= 0. "
                    + "No differentiability at zero is needed when 1 <= n < 2.")),
            Paragraph(Text("Differentiating A gives A'(r)=n r^(n-2) J(r^2)/(1-r^(2n))^2, hence A' >= 0. "
                + "The derivative of B is -2 T/(1+r)^2 - 2n((1-r)/(1+r))r^(n-1)/(1+r^n)^2, which is strictly negative. "
                + "Since A and B are positive, F'=A'/(1+B)-(1+A)B'/(1+B)^2 is strictly positive. "
                + "At n=1 the J term vanishes, but the B term remains strictly negative.")),
            Paragraph(Text("The consumers are the alpha-at-least-two and below-one clauses of C. Hirche, Renyi Bounds on Information Combining, "
                + "ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18. This certificate supplies the real-order "
                + "one-variable inequalities: F is nondecreasing for n >= 1 (alpha >= 2) and antitone for -1 < n < 0 (0 < alpha < 1).")))));

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
