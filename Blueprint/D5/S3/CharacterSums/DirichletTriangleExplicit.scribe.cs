using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletTriangleExplicitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/DirichletTriangleExplicit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered Dirichlet triangular explicit formula",
        H("The centered Dirichlet triangular explicit formula"), Blocks(
            Describe.Lean(DescribeId.Create("dirichlet-centered-zero-kernel"),
                DeclarationHandle.Create(Prefix + "zeroKernel"), H("The centered zero kernel"),
                StatementSource.FromAuthor(Disp(KernelDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three terms are grouped before summation. Each denominator is nonzero " +
                    "at a zero of a primitive nonprincipal completion. At x=1 the grouped kernel " +
                    "vanishes. Powers use the complex principal power of the positive real x."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dirichlet-centered-zero-sum"),
                DeclarationHandle.Create(Prefix + "zeroTriangle"), H("The actual zero divisor"),
                StatementSource.FromAuthor(Disp(SumDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index consists of distinct zeros of the actual modulus-normalized " +
                    "completion. The coefficient m is its analytic order. Thus multiplicity is " +
                    "counted exactly once. The three coefficient sums are absolutely convergent; " +
                    "no separate sum of reciprocal zeros is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dirichlet-triangular-explicit-formula"),
                DeclarationHandle.Create(Prefix + "characterTriangle_explicit"),
                H("The exact explicit formula"),
                StatementSource.FromAuthor(Disp(ExplicitStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here S is characterTriangle, Z is zeroTriangle, ell is the actual " +
                    "logarithmic derivative of the Dirichlet L-function; " +
                    "C is parityCorrection. " +
                    "For even characters C is 1-log(x)+(log(2)-1)/x minus the full even trivial " +
                    "tail. For odd characters C is -1+(log(x)+2-log(2))/x minus x inverse " +
                    "times the existing full trivial tail. " +
                    "The conductor and Euler constants " +
                    "cancel after centering the completed logarithmic derivative at two.")),
                    Paragraph(Text(
                    "The arithmetic Laplace transform comes from DirichletTrianglePerron. " +
                    "The two-point difference formula supplies the three convergent zero " +
                    "coefficients. Absolute domination justifies the spectral Laplace exchange. " +
                    "The centered zero transform is (H(s)-H(2))/(s(s+1)); the parity correction " +
                    "has transform (psi((s+a)/2)-psi((2+a)/2))/(2s(s+1)). Their sum is the " +
                    "actual negative Dirichlet logarithmic derivative divided by s(s+1). " +
                    "Fourier inversion and the already proved Perron formula then recover S. " +
                    "The excluded Fourier frequency has measure zero. The endpoint " +
                    "x=1 follows from the exact trivial-tail masses. No RH assumption is used.")),
                    Paragraph(Text(
                    "Primitivity supplies reflection and the zero strip of the completion. " +
                    "The nonprincipal assumption supplies entireness without a pole correction. " +
                    "The half-axis x>=1 is the convergence domain of the trivial tails, and " +
                    "the initial endpoint is included by its exact vanishing. This is an " +
                    "application of the cited factorization and inversion theorems; the name " +
                    "of the explicit formula does not by itself assert a new escape witness."))),
                DescribeRole.Theorem))));

    private static Formula KernelDefinition()
    {
        var rho = V("rho"); var x = V("x");
        var first = Div(Pow(x, rho), Mul(rho, Add(rho, D(1))));
        var second = Div(D(2), Mul(rho, Sub(D(2), rho)));
        var third = Div(D(3), Mul(Mul(x, Add(rho, D(1))), Sub(D(2), rho)));
        return All("rho", C(), All("x", R(), Eq(Call("K", rho, x),
            Add(Sub(first, second), third))));
    }

    private static Formula SumDefinition()
    {
        var rho = V("rho"); var x = V("x"); var chi = V("chi");
        var index = Seq(rho, Sp, InMacro, Sp, Call("zeros", chi));
        var sum = Seq(new Formula.Subscript(F.Sum, index), Sp,
            Grp(Mul(Call("m", chi, rho), Call("K", rho, x))));
        return All("q", N(), All("chi", Call("DirichletCharacter", C(), V("q")),
            All("x", R(), Eq(Call("Z", chi, x), sum))));
    }

    private static Formula ExplicitStatement()
    {
        var chi = V("chi"); var x = V("x");
        var rhs = Add(Sub(Neg(Call("Z", chi, x)),
            Mul(Sub(D(1), Div(D(1), x)), Call("ell", chi, D(2)))), Call("C", chi, x));
        return All("q", N(), Imp(Lt(D(0), V("q")),
            All("chi", Call("DirichletCharacter", C(), V("q")),
                Imp(Call("primitive", chi), Imp(Ne(chi, D(1)),
                    All("x", R(), Imp(Le(D(1), x), Eq(Call("S", chi, x), rhs))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula R() => Seq(Mathbb, Grp(V("R")), Sp);
    private static Formula C() => Seq(Mathbb, Grp(V("C")), Sp);
    private static Formula N() => Seq(Mathbb, Grp(V("N")), Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name)), Sp), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => Sub(D(0), a);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
}
