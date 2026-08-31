using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class CountableRationalFluxCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaAnalytic/CountableRationalFluxCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational rectangles detect every isolated zero in the open right half-plane.",
        H("Countable Rational Flux Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("countable-rational-flux-criterion"),
            DeclarationHandle.Create(Prefix + "countable_rational_flux_criterion"),
            H("Countable rational flux criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Axis isolation gives a real rectangle containing only the selected zero. "
                    + "Density of the rationals supplies four rational sides strictly between "
                    + "that zero and the isolating sides. The canonical rectangle boundary then "
                    + "contains no zero, while the selected zero lies in its interior. The public "
                    + "flux law converts this enclosure into a nonzero flux certificate."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Not(Formula proposition) => new Formula.Not(proposition);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real"), rational = Call("Rat"), natural = Call("Nat");
        Formula complex = Call("Complex"), zeros = F.Id("zeros"), flux = F.Id("flux");
        Formula z = F.Id("z"), w = F.Id("w");
        Formula x0 = F.Id("x0"), x1 = F.Id("x1");
        Formula y0 = F.Id("y0"), y1 = F.Id("y1");
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");

        Formula Re(Formula value) => Call("re", value);
        Formula Im(Formula value) => Call("im", value);
        Formula Corner(Formula x, Formula y) => Call("ComplexMk", x, y);
        Formula Rectangle(Formula left, Formula right) => Call("Rectangle", left, right);
        Formula Border(Formula left, Formula right) => Call("RectangleBorder", left, right);
        Formula Mem(Formula value, Formula set) => Call("mem", value, set);
        Formula NotMem(Formula value, Formula set) => Not(Mem(value, set));
        Formula FluxAt() => Apply(flux, a, b, c, d);

        Formula outerRectangle = Rectangle(Corner(x0, y0), Corner(x1, y1));
        Formula rationalRectangle = Rectangle(
            Corner(Call("toReal", a), Call("toReal", c)),
            Corner(Call("toReal", b), Call("toReal", d)));
        Formula rationalBorder = Border(
            Corner(Call("toReal", a), Call("toReal", c)),
            Corner(Call("toReal", b), Call("toReal", d)));

        Formula uniqueInOuter = ForAll(
            [Bound("w", complex)],
            Implies(
                And(Mem(w, zeros), Mem(w, outerRectangle)),
                Equal(w, z)));
        Formula axisIsolation = ForAll(
            [Bound("z", complex)],
            Implies(
                And(Mem(z, zeros), Greater(Re(z), D(0))),
                Exists(
                    [Bound("x0", real), Bound("x1", real),
                        Bound("y0", real), Bound("y1", real)],
                    All(
                        Greater(x0, D(0)),
                        Less(x0, Re(z)),
                        Less(Re(z), x1),
                        Less(y0, Im(z)),
                        Less(Im(z), y1),
                        uniqueInOuter))));

        Formula rationalSideConditions = All(
            Greater(a, D(0)), Less(a, b), Less(c, d));
        Formula boundaryFree = ForAll(
            [Bound("z", complex)],
            Implies(Mem(z, rationalBorder), NotMem(z, zeros)));
        Formula rectangleZeroFree = ForAll(
            [Bound("z", complex)],
            Implies(Mem(z, zeros), NotMem(z, rationalRectangle)));
        Formula localFluxLaw = ForAll(
            [Bound("a", rational), Bound("b", rational),
                Bound("c", rational), Bound("d", rational)],
            Implies(
                And(rationalSideConditions, boundaryFree),
                Iff(Equal(FluxAt(), D(0)), rectangleZeroFree)));

        Formula noRightHalfPlaneZero = ForAll(
            [Bound("z", complex)],
            Implies(Mem(z, zeros), Not(Greater(Re(z), D(0)))));
        Formula everyBoundaryFreeFluxVanishes = ForAll(
            [Bound("a", rational), Bound("b", rational),
                Bound("c", rational), Bound("d", rational)],
            Implies(
                And(rationalSideConditions, boundaryFree),
                Equal(FluxAt(), D(0))));
        Formula conclusion = Iff(noRightHalfPlaneZero, everyBoundaryFreeFluxVanishes);

        Formula fluxType = Arrow(rational,
            Arrow(rational, Arrow(rational, Arrow(rational, natural))));
        return F.Disp(ForAll(
            [Bound("zeros", Call("Set", complex)), Bound("flux", fluxType)],
            Implies(And(axisIsolation, localFluxLaw), conclusion)));
    }
}
