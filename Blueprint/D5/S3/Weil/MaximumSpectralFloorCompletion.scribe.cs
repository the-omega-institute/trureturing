using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class MaximumSpectralFloorCompletionDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/MaximumSpectralFloorCompletion.maximum_spectral_floor_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual positivity and full-spectrum white-floor feasibility have the same maximum.",
        H("Maximum Spectral-Floor Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("maximum-spectral-floor-completion"),
            DeclarationHandle.Create(Handle),
            H("Maximum spectral-floor completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The positive spectrum carrier packages nonnegativity. A floor is locally "
                        + "feasible when removing its normalized white reading leaves the reading "
                        + "of a positive residual spectrum.")),
                Paragraph(Text(
                    "From a local residual, adding the white spectrum constructs an explicit "
                        + "full-spectrum witness. Conversely, a full-spectrum decomposition "
                        + "returns its residual as the local witness.")),
                Paragraph(Text(
                    "Thus the two feasible-floor predicates agree pointwise. Their defining "
                        + "sets are equal, so their conditionally complete suprema are equal, "
                        + "including the empty or unbounded cases supplied by NNReal."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula spectrum = F.Id("Spectrum");
        Formula reading = F.Id("Reading");
        Formula check = F.Id("check");
        Formula white = F.Id("white");
        Formula delta = F.Id("delta");
        Formula source = F.Id("source");
        Formula floor = F.Id("floor");
        Formula nnreal = Call("NNReal");

        Formula residualFeasible =
            Call("ResidualFeasible", check, delta, source, floor);
        Formula fullSpectrumFeasible =
            Call("FullSpectrumFeasible", check, white, source, floor);
        Formula pointwiseEquivalence = ForAll(
            [Bound("floor", nnreal)],
            Iff(residualFeasible, fullSpectrumFeasible));
        Formula normalization = ForAll(
            [Bound("floor", nnreal)],
            Equal(
                Apply(check, Apply(white, floor)),
                Multiply(Call("toReal", floor), delta)));
        Formula residualFloors = SetOf(floor, residualFeasible);
        Formula fullSpectrumFloors = SetOf(floor, fullSpectrumFeasible);
        Formula equalSuprema = Equal(
            Call("sSup", residualFloors),
            Call("sSup", fullSpectrumFloors));

        return Disp(ForAll(
            [
                Bound("Spectrum", type),
                Bound("Reading", type),
                Bound("check", Call("AddMonoidHom", spectrum, reading)),
                Bound("white", Arrow(nnreal, spectrum)),
                Bound("delta", reading),
                Bound("source", reading),
            ],
            Implies(normalization, And(pointwiseEquivalence, equalSuprema))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula SetOf(Formula element, Formula predicate) =>
        Seq(OpenBrace, element, Sp, Mid, Sp, predicate, CloseBrace);
}
