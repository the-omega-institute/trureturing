using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletTriangleBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/DirichletTriangleBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-height triangular character bounds", H("Finite-height character bounds"), Blocks(
            Describe.Lean(DescribeId.Create("triangle-finite-height"),
                DeclarationHandle.Create(Prefix + "characterTriangle_finite_height"),
                H("The quantitative finite-height estimate"),
                StatementSource.FromAuthor(Disp(GeneralStatement())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Here chi is primitive and nonprincipal, x is at least one, and T>32. " +
                    "Nonvanishing means that L(s,chi) has no zero with Re(s)>1/2 and " +
                    "absolute imaginary part at most T. P is the real completed logarithmic " +
                    "derivative at two; ell is the ordinary logarithmic derivative at two. " +
                    "The correction c is the full parity correction in the explicit formula. " +
                    "The bound retains both actual endpoint terms. " +
                    "Reflection sends rho to one minus its conjugate, preserving its " +
                    "imaginary part. Thus every zero with absolute height at most T is on " +
                    "the critical line. The high tail has strictly greater height than T. " +
                    "Zeros are indexed by distinct location with actual analytic multiplicity. " +
                    "The completed vertical estimate supplies the Poisson envelope with " +
                    "effective conductor equal to q; no conductor enlargement is suppressed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-prime-bound"),
                DeclarationHandle.Create(Prefix + "characterTriangle_prime_bound"),
                H("The primitive-character endpoint"),
                StatementSource.FromAuthor(Disp(PrimeStatement())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every modulus p at least 10000 and every primitive character, " +
                    "nonvanishing in the closed height window of radius four square roots " +
                    "of p implies the displayed estimate. Its rational coefficient is " +
                    "strictly below three halves, with gap 3209/222750. " +
                    "The finite rational budget combines the full positive Poisson mass, " +
                    "the ordinary reciprocal-square tail and the parity correction. " +
                    "Strictness comes from this positive rational gap, rather than a " +
                    "strict inequality passed from finite sums to an infinite tail. " +
                    "These are uniform analytic inequalities over an unbounded domain."))), DescribeRole.Theorem))));

    private static Formula GeneralStatement()
    {
        var x = V("x"); var q = V("q"); var chi = V("chi"); var t = V("T");
        var a = Add(Add(Mul(D(2), Call("sqrt", x)), D(4)), Div(D(2), x));
        var b = Add(Add(x, D(2)), Div(D(3), x));
        var bound = Add(Add(Mul(a, Call("P", chi)), Mul(b, Call("tail", q, t))),
            Add(Mul(Sub(D(1), Div(D(1), x)), Call("norm", Call("ell", chi))),
                Call("norm", Call("c", chi, x))));
        return All("q", N(), All("chi", Call("characters", q), All("x", R(),
            All("T", R(), Imp(Call("admissible", q, chi, x, t),
                Le(Call("norm", Call("S", chi, x)), bound))))));
    }

    private static Formula PrimeStatement()
    {
        var p = V("p"); var chi = V("chi");
        return All("p", N(), All("chi", Call("characters", p),
            Imp(Call("primitiveadmissible", p, chi), Le(Call("norm", Call("S", chi, p)),
                Sub(Mul(Mul(Div(D(1,6,5,4,5,8), D(1,1,1,3,7,5)),
                    Call("sqrt", p)), Call("log", p)), Div(D(1), p))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula R() => Seq(Mathbb, Grp(V("R")), Sp);
    private static Formula N() => Seq(Mathbb, Grp(V("N")), Sp);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n)), Sp), [.. args]);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
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
}
