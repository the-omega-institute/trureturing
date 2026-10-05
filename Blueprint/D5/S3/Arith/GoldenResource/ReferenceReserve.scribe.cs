using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ReferenceReserveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime optimizer reserve has a uniform truncation tail at every finite root scale.",
        H("Reference Reserve at Finite Root Scales"),
        Blocks(
            Paragraph(Text("For x > 1 let lambda_x = 1/(x log x), v(x,p) = floor(log x/log p), "
                + "g(x,p,a) = Q_a(1/p) - lambda_x a log p, and "
                + "f(x,p,a) = log S_a(1/p) - lambda_x a log p. "
                + "The prefixes S and Q are the finite geometric and harmonic power prefixes. "
                + "For prime p define r(x,p) = g(x,p,v(x,p)) - sup_a f(x,p,a); "
                + "for nonprime p put r(x,p) = 0. This is the function reserve in the theorem. "
                + "Define R(x) as the sum of r(x,p) for natural p < ceil(x), and R_K(x) "
                + "as the same sum restricted to p > x^(1/K). These are totalReserve and "
                + "truncatedReserve. The vanishing of r(x,p) for p >= x makes these "
                + "the full prime sum and the sum over x^(1/K) < p <= x respectively.")),
            Describe.Lean(
                DescribeId.Create("reference-reserve-finite-root-tail"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/ReferenceReserve.result"),
                H("Finite support, uniform tail, and retained exponent bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The actual supremum is attained. At every prime, its value "
                        + "and hence the reserve are independent of choices among tied maximizers. "
                        + "The k-th reference increment is nonnegative exactly when p^k <= x: "
                        + "after multiplying positive denominators this is the monotonicity of y log y. "
                        + "Consequently v(x,p) maximizes g. Comparing the logarithmic geometric "
                        + "prefix with Q gives 0 <= r(x,p) <= D_(v(x,p))(1/p). The finite-prefix "
                        + "deficit bound gives r(x,p) <= p^(-v(x,p)-1) < 1/x. When p >= x "
                        + "every reference increment is nonpositive, both maxima are zero, "
                        + "and the reserve vanishes.")),
                    Paragraph(Text("Put t = x^(1/(K+1)). The omitted primes split into those at "
                        + "most t and those between t and x^(1/K). The first set has at most t "
                        + "members and each contributes at most 2/x. Every prime in the second "
                        + "set has reference exponent exactly K and contributes at most 2p^(-K-1). "
                        + "For an arbitrary finite set of integers above t >= 1, decreasing-power "
                        + "integral comparison bounds its sum of n^(-K-1) by "
                        + "(1+1/K)t^(-K). Combining the two sets and using t/x = t^(-K) "
                        + "gives (4+2/K)x^(-K/(K+1)).")),
                    Paragraph(Text("If x >= K^K and p > x^(1/K), then p > K and "
                        + "log x < K log p < p log p. Thus p^(K+1) log p > x log x. "
                        + "The reciprocal-power marginal bound makes layer K+1 strictly "
                        + "unprofitable. Strict decrease of the marginals makes the actual "
                        + "objective strictly decreasing from K onwards, so every actual "
                        + "maximizer has exponent at most K."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula x = F.Id("x"), p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), k = F.Id("K");
        Formula r = Call("r", x, p);
        Formula maximizing = All([Bound("b", Naturals())], Leq(Call("f", x, p, b), Call("f", x, p, a)));
        Formula maximumValue = Exists([Bound("a", Naturals())], And(maximizing,
            Equal(r, Sub(Call("g", x, p, Call("v", x, p)), Call("f", x, p, a)))));
        Formula attained = All([Bound("p", Naturals())], Implies(Call("Prime", p), maximumValue));
        Formula difference = Sub(Call("R", x), new Formula.Apply(Seq(F.Id("R"), Underscore, k), [x]));
        Formula coefficient = Add(D(4), new Formula.Fraction(D(2), k));
        Formula power = new Formula.Power(x, new Formula.Fraction(Seq(Minus, k), Add(k, D(1))));
        Formula tail = All([Bound("K", Naturals())], Implies(Leq(D(2), k),
            And(Leq(D(0), difference), Leq(difference, Seq(Open, coefficient, Close, Sp, power)))));
        Formula root = new Formula.Power(x, new Formula.Fraction(D(1), k));
        Formula exponentBound = All([Bound("K", Naturals())],
            Implies(And(Leq(D(2), k), Leq(new Formula.Power(k, k), x)),
                All([Bound("p", Naturals())], Implies(And(Call("Prime", p), Less(root, p)),
                    All([Bound("a", Naturals())], Implies(maximizing, Leq(a, k)))))));
        return Disp(All([Bound("x", Reals())], Implies(Less(D(1), x),
            And(Call("Finite", Call("support", Call("r", x))), And(attained, And(tail, exponentBound))))));
    }

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) => new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Exists(Formula.BoundVariable[] vars, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Equal(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Leq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Less(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Add(Formula l, Formula r) => Seq(l, Plus, r);
    private static Formula Sub(Formula l, Formula r) => Seq(l, Minus, r);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
