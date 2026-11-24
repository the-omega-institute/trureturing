using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class TriangleRampDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/TriangleRamp.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangular weights from affine ramps", H("Triangular weights from affine ramps"), Blocks(
            Describe.Lean(DescribeId.Create("triangle-remove-average"),
                DeclarationHandle.Create(Prefix + "removeAverage"), H("Removing the running average"),
                StatementSource.FromAuthor(Disp(AverageDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral is the oriented real interval integral from one to x. " +
                    "Write D(f,x) for removeAverage(f,x)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangle-affine-ramp"),
                DeclarationHandle.Create(Prefix + "ramp"), H("An affine positive part"),
                StatementSource.FromAuthor(Disp(RampDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ramp is zero at its entry point, so inclusive and strict cutoffs " +
                    "give the same weighted value there."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangle-kernel-change"),
                DeclarationHandle.Create(Prefix + "removeAverage_ramp"), H("The exact change of kernel"),
                StatementSource.FromAuthor(Disp(RampStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Split the integral at n. Its nonzero part is (x-n)^2/(2n). " +
                    "For x below n both sides vanish. The formula holds for every positive x. " +
                    "At n=x the common value is zero. The lower bound n>=1 is essential: " +
                    "n=1/2 and x=1 give different sides."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-root-envelope"),
                DeclarationHandle.Create(Prefix + "removeAverage_sqrt_bound"), H("A square-root envelope"),
                StatementSource.FromAuthor(Disp(EnvelopeStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integrating sqrt(t) gives 2(x sqrt(x)-1)/3. The triangle inequality " +
                    "therefore retains the gain 4C/(3x) from the lower endpoint. " +
                    "No measurability or integrability assumption on f is needed. " +
                    "At x=1 the estimate reduces to the assumed pointwise bound. " +
                    "For x>1, f(t)=C sqrt(t) except for f(x)=-C sqrt(x) attains the bound; " +
                    "thus the coefficient and endpoint term are sharp for this envelope class."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-main-term"),
                DeclarationHandle.Create(Prefix + "removeAverage_main"), H("The exact main term"),
                StatementSource.FromAuthor(Disp(MainStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The antiderivative is t^2 log(t)/2-t^2/4-a t^2/2. " +
                    "The identity holds on the whole positive half-axis, including x<1 " +
                    "with the oriented integral."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-concave-endpoints"),
                DeclarationHandle.Create(Prefix + "affine_sqrt_ge_endpoints"), H("Endpoint minima"),
                StatementSource.FromAuthor(Disp(EndpointStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reciprocal is convex on the positive half-axis and the square root " +
                    "is concave. Consequently A-B/x-x/2+sqrt(x) is concave for B>=0. " +
                    "Its value on a closed interval is at least the smaller endpoint value. " +
                    "The upper endpoint is positive as a consequence of the other assumptions. " +
                    "Equality holds when x is an endpoint with the smaller value."))),
                DescribeRole.Theorem))));

    private static Formula AverageDefinition() => All("f", new Formula.TypeArrow(R(), R()),
        All("x", R(), Eq(Call("D", V("f"), V("x")), Sub(Call("f", V("x")),
            Mul(Div(D(2), V("x")), Call("integral", D(1), V("x"), V("f")))))));
    private static Formula RampDefinition() => All("n", R(), All("t", R(),
        Eq(Call("ramp", V("n"), V("t")),
            Call("max", Sub(Div(V("t"), V("n")), D(1)), D(0)))));
    private static Formula RampStatement() => All("n", R(), All("x", R(),
        Imp(Le(D(1), V("n")), Imp(Lt(D(0), V("x")),
            Eq(Call("D", Call("ramp", V("n")), V("x")),
                Call("max", Sub(D(1), Div(V("n"), V("x"))), D(0)))))));
    private static Formula EnvelopeStatement()
    {
        var c = V("C"); var x = V("x");
        var bound = All("t", R(), Imp(Mem(V("t"), Call("Icc", D(1), x)),
            Le(Call("abs", Call("f", V("t"))), Mul(c, Sqrt(V("t"))))));
        return All("f", new Formula.TypeArrow(R(), R()), All("C", R(), All("x", R(),
            Imp(Le(D(1), x), Imp(bound, Le(Call("abs", Call("D", V("f"), x)),
                Sub(Mul(Div(Mul(D(7), c), D(3)), Sqrt(x)),
                    Div(Mul(D(4), c), Mul(D(3), x)))))))));
    }
    private static Formula MainStatement()
    {
        var a = V("a"); var x = V("x"); var t = V("t");
        var f = Seq(Open, LambdaLower, Sp, t, Colon, R(), Sp, Mapsto, Sp,
            Sub(Mul(t, Call("log", t)), Mul(a, t)), Close);
        return All("a", R(), All("x", R(), Imp(Lt(D(0), x),
            Eq(Call("D", f, x), Sub(Div(x, D(2)), Div(Add(a, Div(D(1), D(2))), x))))));
    }
    private static Formula Error(Formula x) =>
        Add(Sub(Sub(V("A"), Div(V("B"), x)), Div(x, D(2))), Sqrt(x));
    private static Formula EndpointStatement() => All("A", R(), All("B", R(),
        All("a", R(), All("b", R(), All("x", R(), Imp(Le(D(0), V("B")),
            Imp(Lt(D(0), V("a")), Imp(Mem(V("x"), Call("Icc", V("a"), V("b"))),
                Le(Call("min", Error(V("a")), Error(V("b"))), Error(V("x")))))))))));

    private static Formula V(string n) => F.Id(n);
    private static Formula R() => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sqrt(Formula a) => Call("sqrt", a);
}
