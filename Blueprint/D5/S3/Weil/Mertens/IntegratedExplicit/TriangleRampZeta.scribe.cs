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
                DeclarationHandle.Create(Prefix + "smoothedMangoldt"),
                H("The strict triangular Mangoldt sum"),
                StatementSource.FromAuthor(Disp(SumDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural range ends at ceil(x)-1, exactly the natural numbers n<x. " +
                    "Lambda is the actual von Mangoldt function and Lambda(0)=Lambda(1)=0. " +
                    "At integer endpoints the entering term has weight zero. " +
                    "For x<=0 the range is empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triangle-zeta-error"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt_explicit_bound"),
                H("The two-sided error with the actual trivial terms"),
                StatementSource.FromAuthor(Disp(ErrorStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The center retains the complete trivial-zero tail and its integral. " +
                    "The error has coefficient 7M/3 and the boundary gain 4M/(3x). At x=1 " +
                    "both sides equal M unconditionally; for x>1 RH supplies the envelope."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-zeta-explicit"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt_explicit_lower"),
                H("An explicit lower bound under RH"),
                StatementSource.FromAuthor(Disp(ExplicitStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M=firstLiMass and gamma be the Euler-Mascheroni constant. " +
                    "The actual integrated explicit formula identifies U(x) with " +
                    "Re(H(log x))+log(2pi)-T(log x), using the same complete ramps as U. " +
                    "Apply the running-average operator to these ramps. Under RH the " +
                    "zero term has envelope M sqrt(x). The operator changes its " +
                    "coefficient to (7/3)M and retains 4M/(3x). " +
                    "The constant term contributes -log(2pi)+2log(2pi)/x. " +
                    "Nonnegativity of the integral of T and T<=1-log(2) give the displayed " +
                    "bound. " +
                    "Since M<1/3, the square-root coefficient is less than 7/9. " +
                    "Thus c2=1+log(pi) and c3=3/2+gamma-2log(2pi)-4M/3 retain " +
                    "both lower-endpoint gains without rounding the constants."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-zeta-uniform"),
                DeclarationHandle.Create(Prefix + "smoothedMangoldt_lower"),
                H("The triangular lower bound under RH"),
                StatementSource.FromAuthor(Disp(UniformStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bound holds for every real x; for x<=0 the sum is empty. " +
                    "For 0<=x<=4, nonnegativity of the sum is sufficient. " +
                    "On [4,5], the terms 2,3,4 give S(x)>=7/3-7/x. " +
                    "On [5,10], the terms 2,3,4,5 give S(x)>=10/3-12/x. " +
                    "Concavity reduces both comparisons to their endpoints, using sqrt(5)>=2 " +
                    "and sqrt(10)>=3. The logarithmic bounds needed are log(2)>=2/3 " +
                    "and log(3)>=1. For x>10 the upper Euler-Mascheroni sequence at 16 " +
                    "gives M<1/8. The explicit lower bound, log(pi)<6/5, and sqrt(x)>=22/7 " +
                    "then give the result. RH supplies the square-root zero envelope; " +
                    "no unconditional version or converse to RH is asserted. " +
                    "The hypothesis is only 10<x implies RH; at and below ten it is vacuous. " +
                    "Equality at x=0 prevents a uniformly positive additive improvement. " +
                    "At x=3, any coefficient c in the bound x/2-c sqrt(x)<=S(x) must satisfy " +
                    "c>=(3/2-log(2)/3)/sqrt(3). Optimality of the unit coefficient is unproved."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-principal-equality"),
                DeclarationHandle.Create(Prefix + "principal_smoothedCharacterSum_eq"),
                H("The full principal Mangoldt sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a prime modulus p, the real principal character sum equals " +
                    "smoothedMangoldt(p). Every nonzero n<p is a unit modulo p and " +
                    "the principal character is one there; Lambda(0)=0 removes the " +
                    "zero term. This identity needs no zero hypothesis and retains " +
                    "prime powers. PrincipalTriangleLower uses it for its unconditional " +
                    "Chebyshev lower bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-principal-main"),
                DeclarationHandle.Create(Prefix + "principal_smoothedCharacterSum_lower"),
                H("The principal character term"),
                StatementSource.FromAuthor(Disp(PrincipalStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For prime p, every positive integer below p is coprime to p. " +
                    "Thus the principal character is one on the contributing integers, " +
                    "and its real triangular sum equals the Mangoldt sum. " +
                    "The RH assumption is used only for p>=10."))), DescribeRole.Theorem))));

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
        var coefficient = Mul(Div(D(7), D(3)), mass);
        var boundary = Sub(Sub(Add(Div(D(3), D(2)), gamma),
            Mul(D(2), Call("log", Mul(D(2), pi)))), Mul(Div(D(4), D(3)), mass));
        var lower = Sub(Sub(Sub(Div(x, D(2)), Mul(coefficient, Sqrt(x))),
            Add(D(1), Call("log", pi))), Div(boundary, x));
        return All("x", R(), Imp(Imp(Lt(D(1), x), V("RiemannHypothesis")),
            Imp(Le(D(1), x), Le(lower, Call("S", x)))));
    }
    private static Formula Center(Formula x)
    {
        var l = Call("log", Mul(D(2), Call("pi")));
        return Add(Sub(Add(Sub(Sub(Div(x, D(2)),
            Div(Add(Div(D(3), D(2)), Call("eulerMascheroniConstant")), x)), l),
            Div(Mul(D(2), l), x)), Call("T", Call("log", x))),
            Mul(Div(D(2), x), Call("integral", D(1), x,
                Seq(Open, LambdaLower, Sp, V("t"), Colon, R(), Sp, Mapsto, Sp,
                    Call("T", Call("log", V("t"))), Close))));
    }
    private static Formula ErrorStatement()
    {
        var x = V("x"); var mass = Call("firstLiMass");
        var bound = Sub(Mul(Mul(Div(D(7), D(3)), mass), Sqrt(x)),
            Div(Mul(Div(D(4), D(3)), mass), x));
        return All("x", R(), Imp(Imp(Lt(D(1), x), V("RiemannHypothesis")),
            Imp(Le(D(1), x), Le(Call("abs", Sub(Call("S", x), Center(x))), bound))));
    }
    private static Formula UniformStatement() => All("x", R(),
        Imp(Imp(Lt(D(1,0), V("x")), V("RiemannHypothesis")),
            Le(Sub(Div(V("x"), D(2)), Sqrt(V("x"))), Call("S", V("x")))));
    private static Formula PrincipalStatement() => All("p", Seq(Mathbb, Grp(V("N")), Sp),
        Imp(Call("Prime", V("p")),
            Imp(Imp(Le(D(1,0), V("p")), V("RiemannHypothesis")),
                Le(Sub(Div(V("p"), D(2)), Sqrt(V("p"))),
                    Call("Re", Call("smoothedCharacterSum", V("p"), D(1)))))));

    private static Formula V(string n) => F.Id(n);
    private static Formula R() => Seq(Mathbb, Grp(V("R")), Sp);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n)), Sp), [.. args]);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
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
