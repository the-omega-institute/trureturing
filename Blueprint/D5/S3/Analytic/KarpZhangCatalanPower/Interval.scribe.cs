using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangCatalanPower;

internal sealed class IntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangCatalanPower/Interval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central Catalan-power convolution intervals increase under balancing.",
        H("Reflected intervals and tail positivity"),
        Blocks(
            Paragraph(Text("All sums are finite. The coefficient a(n,t) is the rising-factorial quotient, and b(j) is its derivative at zero. Natural subtraction occurs only under the stated finite bounds. The boundary filter also handles empty signed intervals without assigning a spurious term to index zero.")),
            Entry("R", "The uncancelled left boundary", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("j", N(),
                    Eq(Call("R", V("m"), V("q"), V("j")), BoundaryBody())))),
                "R contains exactly the nonnegative integers in [max(0,q-j), min(q-1,m-q-j)], where the upper endpoint is an integer. Its filter presentation retains the condition i+j≤m-q, so the set is empty when the signed upper endpoint is negative."),
            Entry("Z", "The central convolution interval", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("u", Rl(), All("v", Rl(),
                    Eq(Z(V("u"), V("v")), IntervalSum(Product(V("k"), V("u"), V("v")))))))),
                "Z(m,q,u,v) sums a(k,u)a(m-k,v) for q≤k≤m-q. The two endpoints are included, including a singleton central interval."),
            Entry("sliceDerivative", "The reflected determinant sum", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("u", Rl(), All("v", Rl(),
                    Eq(Call("sliceDerivative", V("m"), V("q"), V("u"), V("v")),
                        FluxBody(V("u"), V("v"))))))),
                "For each j from one through m, multiply b(j) by the sum over R(m,q,j) of the degree-parameter determinants with total degree m-j. This is the derivative of Z along a constant-sum line."),
            Entry("reflected_interval", "Cancellation of two reflected intervals", DescribeRole.Theorem,
                All("m", N(), All("q", N(), All("j", N(),
                    Imp(Le(Mul(D(2), V("q")), V("m")), Imp(Le(V("j"), V("m")),
                        All("w", Arrow(N(), Rl()), Eq(
                            Sub(Sum("i", Window(true), Call("w", V("i"))),
                                Sum("i", Window(false), Call("w", V("i")))),
                            Sum("i", Call("R", V("m"), V("q"), V("j")),
                                Sub(Call("w", V("i")), Call("w", Sub(Sub(V("m"), V("j")), V("i")))))))))))),
                "Restrict both intervals to 0≤i≤m-j. Reflection i↦m-j-i exchanges them. The common part cancels, and the remaining terms pair over R. The identity holds for every real-valued weight w, with no sign assumption."),
            Entry("hasDerivAt_slice", "The constant-sum slice derivative", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(Mul(D(2), V("q")), V("m")),
                    All("S", Rl(), All("r", Rl(), Imp(Lt(D(0), V("r")),
                        Imp(Lt(D(0), Sub(V("S"), V("r"))),
                            Call("HasDerivAt", Slice(), Call("sliceDerivative", V("m"), V("q"),
                                V("r"), Sub(V("S"), V("r"))), V("r"))))))))),
                "Differentiate every finite summand. The coefficient derivative identity expands each factor into a lower-degree convolution. Two explicit triangular bijections collect terms with the same j. Reflection then converts their difference into the determinant sum."),
            Entry("Z_symm", "Reflection symmetry of the interval convolution", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(Mul(D(2), V("q")), V("m")),
                    All("u", Rl(), All("v", Rl(), Eq(Z(V("u"), V("v")), Z(V("v"), V("u")))))))),
                "The map k↦m-k permutes the closed central interval and exchanges the two coefficient factors. Balancing can therefore choose the smaller parameter as the first coordinate."),
            Entry("slice_strictMonoOn", "Strict increase toward the midpoint", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(D(1), V("q")),
                    Imp(Le(Mul(D(2), V("q")), V("m")), All("S", Rl(),
                        Imp(Lt(D(0), V("S")),
                            Call("StrictMonoOn", Slice(), App(Qualified("Set", "Ioc"), D(0),
                                new Formula.Fraction(V("S"), D(2)))))))))),
                "On the open left half of a positive constant-sum slice, every determinant is positive whenever its boundary set is nonempty. Every b(j) is positive. The j=1 boundary contains q-1, and its two degrees are strictly ordered, so the derivative is strictly positive. The mean-value theorem gives strict increase on (0,S/2], including comparisons with the midpoint."),
            Entry("tail_nonneg", "Every shifted central tail is nonnegative", DescribeRole.Theorem,
                All("m", N(), All("q", N(),
                    Imp(Le(Mul(D(2), V("q")), V("m")),
                        All("mu", Rl(), All("alpha", Rl(), All("beta", Rl(),
                            Imp(Le(D(0), V("mu")), Imp(Le(D(0), V("alpha")),
                                Imp(Le(D(0), V("beta")), Le(D(0), IntervalSum(Delta()))))))))))),
                "The case q=0 is the full convolution: both products have the same total parameter, so the index law makes their difference zero. For q positive and mu positive, keep S=2mu+alpha+beta fixed and compare mu with mu+min(alpha,beta) on (0,S/2]. Symmetry supplies the correct ordering of the two shifted parameters. If q is positive and mu=0, every index in the tail is positive, so a(k,0)=0 and the remaining product is nonnegative. No limiting argument or additional positivity hypothesis on mu is required."))));

    private static DocumentBlock Entry(string declaration, string title, DescribeRole role,
        Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("karp-zhang-interval-" + declaration.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rl() => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sum(string index, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(V(index), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, Rl())),
            Sp, Mapsto, Sp, body));
    private static Formula NatLambda(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, N())),
            Sp, Mapsto, Sp, body));
    private static Formula Range() =>
        App(Qualified("Finset", "range"), Add(Sub(V("m"), V("j")), D(1)));
    private static Formula Bounds(bool left) => left
        ? And(Le(V("q"), Add(V("i"), V("j"))), Le(Add(V("i"), V("j")), Sub(V("m"), V("q"))))
        : And(Le(V("q"), V("i")), Le(V("i"), Sub(V("m"), V("q"))));
    private static Formula Window(bool left) =>
        App(Qualified("Finset", "filter"), NatLambda("i", Bounds(left)), Range());
    private static Formula BoundaryBody() =>
        App(Qualified("Finset", "filter"),
            NatLambda("i", And(Bounds(true), Lt(V("i"), V("q")))), Range());
    private static Formula Z(Formula u, Formula v) => Call("Z", V("m"), V("q"), u, v);
    private static Formula IntervalSum(Formula body) =>
        Sum("k", App(Qualified("Finset", "Icc"), V("q"), Sub(V("m"), V("q"))), body);
    private static Formula Product(Formula k, Formula u, Formula v) =>
        Mul(Call("a", k, u), Call("a", Sub(V("m"), k), v));
    private static Formula Slice() => Lambda("x", Z(V("x"), Sub(V("S"), V("x"))));
    private static Formula FluxBody(Formula u, Formula v) =>
        Sum("j", App(Qualified("Finset", "Icc"), D(1), V("m")),
            Mul(Call("b", V("j")),
                Sum("i", Call("R", V("m"), V("q"), V("j")),
                    Sub(Mul(Call("a", V("i"), u), Call("a", Sub(Sub(V("m"), V("j")), V("i")), v)),
                        Mul(Call("a", Sub(Sub(V("m"), V("j")), V("i")), u), Call("a", V("i"), v))))));
    private static Formula Delta() =>
        Sub(Product(V("k"), Add(V("mu"), V("alpha")), Add(V("mu"), V("beta"))),
            Product(V("k"), V("mu"), Add(Add(V("mu"), V("alpha")), V("beta"))));
}
