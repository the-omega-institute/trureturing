using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class TriangleRampZetaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/TriangleRampZeta.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triangular Mangoldt main term", H("The triangular Mangoldt main term"), Blocks(
            Describe.Lean(DescribeId.Create("triangle-mangoldt-sum"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt"), H("The strict triangular Mangoldt sum"),
                StatementSource.FromAuthor(Disp(SumDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural range ends at ceil(x)-1, exactly the natural numbers n<x. " +
                    "Lambda is the actual von Mangoldt function and Lambda(0)=Lambda(1)=0. " +
                    "At integer endpoints the entering term has weight zero. " +
                    "For x<=0 the range is empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangle-zeta-explicit"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt_explicit_lower"), H("An explicit lower bound under RH"),
                StatementSource.FromAuthor(Disp(ExplicitStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M=firstLiMass and gamma be the Euler-Mascheroni constant. " +
                    "The actual integrated explicit formula identifies U(x) with " +
                    "Re(H(log x))+log(2pi)-T(log x), using the same complete ramps as U. " +
                    "Apply the running-average operator to these ramps. Under RH the " +
                    "zero term has envelope (101/100)M sqrt(x). The operator changes its " +
                    "coefficient to (707/300)M and retains 101M/(75x). " +
                    "The constant term contributes -log(2pi)+2log(2pi)/x. " +
                    "Nonnegativity of the integral of T and T<=1-log(2) give the displayed bound. " +
                    "Since M<1/3, the square-root coefficient is less than 707/900. " +
                    "Thus c2=1+log(pi) and c3=3/2+gamma-2log(2pi)-101M/75 retain " +
                    "both lower-endpoint gains without rounding the constants."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-zeta-uniform"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt_lower"), H("The triangular lower bound under RH"),
                StatementSource.FromAuthor(Disp(UniformStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bound holds for every real x; for x<=0 the sum is empty. " +
                    "For 0<=x<=4, nonnegativity of the sum is sufficient. " +
                    "On [4,5], the terms 2,3,4 give S(x)>=7/3-7/x. " +
                    "On [5,10], the terms 2,3,4,5 give S(x)>=10/3-12/x. " +
                    "Concavity reduces both comparisons to their endpoints, using sqrt(5)>=2 " +
                    "and sqrt(10)>=3. The logarithmic bounds needed are log(2)>=2/3 " +
                    "and log(3)>=1. For x>=10 the upper Euler-Mascheroni sequence at 16 " +
                    "gives M<1/8. The explicit lower bound, log(pi)<6/5, and sqrt(x)>=22/7 " +
                    "then give the result. RH supplies the square-root zero envelope; " +
                    "no unconditional version or converse to RH is asserted. " +
                    "Equality at x=0 prevents a uniformly positive additive improvement. " +
                    "At x=3, any coefficient c in the bound x/2-c sqrt(x)<=S(x) must satisfy " +
                    "c>=(3/2-log(2)/3)/sqrt(3). Optimality of the unit coefficient is unproved."))),
                DescribeRole.Theorem))));

    private static Formula SumDefinition()
    {
        var x = V("x"); var n = V("n");
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(n, Sp, InMacro, Sp, Call("range", Call("ceil", x)))), Sp,
            Grp(Mul(Call("Lambda", n), Sub(D(1), Div(n, x)))));
        return All("x", R(), Eq(Call("S", x), sum));
    }
    private static Formula ExplicitStatement()
    {
        var x = V("x"); var mass = Call("firstLiMass");
        var gamma = Call("eulerMascheroniConstant"); var pi = Call("pi");
        var coefficient = Mul(Div(D(7,0,7), D(3,0,0)), mass);
        var boundary = Sub(Sub(Add(Div(D(3), D(2)), gamma),
            Mul(D(2), Call("log", Mul(D(2), pi)))), Mul(Div(D(1,0,1), D(7,5)), mass));
        var lower = Sub(Sub(Sub(Div(x, D(2)), Mul(coefficient, Sqrt(x))),
            Add(D(1), Call("log", pi))), Div(boundary, x));
        return Imp(V("RiemannHypothesis"), All("x", R(),
            Imp(Le(D(1), x), Le(lower, Call("S", x)))));
    }
    private static Formula UniformStatement() => Imp(V("RiemannHypothesis"),
        All("x", R(), Le(Sub(Div(V("x"), D(2)), Sqrt(V("x"))), Call("S", V("x")))));

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
