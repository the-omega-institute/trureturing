using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CayleyCriticalLineZetaCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Midline/Cayley/CayleyCriticalLineZetaCriterion."
            + "cayley_critical_line_zeta_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical Cayley unit circle is the critical line, and radial neutrality "
            + "of all nontrivial zeta zeros characterizes the Riemann hypothesis.",
        H("Cayley Critical-Line Zeta Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("cayley-critical-line-zeta-criterion"),
            DeclarationHandle.Create(Handle),
            H("Cayley critical-line zeta criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The coefficient c(s) is the imported canonical Cayley coordinate "
                        + "(s - 1)/s. Its norm is one exactly when the real part of s is "
                        + "one half; Lean's totalized value at zero satisfies the same "
                        + "equivalence because neither side holds there.")),
                Paragraph(Text(
                    "The radial quantity beta(rho) is the imported logarithmic radial "
                        + "defect log |c(rho)|. The nontrivial-zero premises are displayed "
                        + "binder for binder from Mathlib's RiemannHypothesis definition. "
                        + "They exclude zero and one, so beta vanishes exactly when the "
                        + "Cayley norm is one."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula complex = Call("Complex");
        Formula s = F.Id("s");
        Formula rho = F.Id("rho");
        Formula n = F.Id("n");
        Formula half = new Formula.Fraction(D(1), D(2));

        Formula coefficient = Call("cayleyCoefficient", s);
        Formula unitCircle = Iff(
            Equal(new Formula.Norm(coefficient), D(1)),
            Equal(Call("re", s), half));
        Formula pointwiseClause = ForAll(
            [Bound("s", complex)],
            unitCircle);

        Formula trivialZero = Exists(
            [Bound("n", natural)],
            Equal(
                rho,
                new Formula.Negate(
                    Multiply(D(2), Add(n, D(1))))));
        Formula zeroPremises = And(
            Equal(Call("riemannZeta", rho), D(0)),
            And(
                new Formula.Not(trivialZero),
                NotEqual(rho, D(1))));
        Formula radialNeutrality = ForAll(
            [Bound("rho", complex)],
            Implies(
                zeroPremises,
                Equal(Call("logarithmicRadialDefect", rho), D(0))));
        Formula zetaClause = Iff(
            Call("RiemannHypothesis"),
            radialNeutrality);

        return Disp(And(pointwiseClause, zetaClause));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
