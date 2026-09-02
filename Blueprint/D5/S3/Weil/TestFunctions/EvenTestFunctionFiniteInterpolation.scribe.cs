using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class EvenTestFunctionFiniteInterpolationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even Weil test functions interpolate finite data at sign-separated complex nodes.",
        H("Finite Interpolation by Even Test Functions"),
        Blocks(Describe.Lean(
            DescribeId.Create("even-weil-test-function-finite-interpolation"),
            DeclarationHandle.Create(Prefix + "even_weilTestFunction_finite_interpolation"),
            H("Even Fourier-Laplace interpolation at sign-separated nodes"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Sign separation makes squaring injective on the finite node set. A scaled "
                    + "even compactly supported smooth seed has nonzero transform at every "
                    + "node, and Lagrange interpolation in the squared nodes supplies an "
                    + "even polynomial differential operator with the prescribed values."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula testFunction = Call("WeilTestFunction");
        Formula set = F.Id("S"), assignment = F.Id("a");
        Formula z = F.Id("z"), w = F.Id("w"), interpolant = F.Id("g");

        Formula Member(Formula value) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
        Formula Apply(Formula function, Formula argument) =>
            new Formula.Apply(function, [argument]);
        Formula Equal(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula NotEqual(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);

        Formula separation = ForAll(
            [Bound("z", complex), Bound("w", complex)],
            Implies(
                Member(z),
                Implies(
                    Member(w),
                    Implies(
                        NotEqual(z, w),
                        NotEqual(z, new Formula.Negate(w))))));
        Formula interpolation = ForAll(
            [Bound("z", set)],
            Equal(
                Call("fourierLaplace", interpolant, z),
                Apply(assignment, z)));
        Formula conclusion = Exists(
            [Bound("g", testFunction)],
            interpolation);

        return Disp(ForAll(
            [Bound("S", Call("Finset", complex))],
            Implies(
                separation,
                ForAll(
                    [Bound("a", new Formula.TypeArrow(set, complex))],
                    conclusion))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
