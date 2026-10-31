using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiveModeProbabilityReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fibers/FiveModeProbabilityReconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical five-event probabilities are reconstructed from three marginal coordinates and one overlap parameter.",
        H("Classical five-mode probability reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-mode-probabilities-sum"),
                DeclarationHandle.Create(Prefix + "probabilities_sum"),
                H("The reconstructed masses sum to one"),
                StatementSource.FromAuthor(Disp(SumFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real X, Y, Z and κ, the five displayed masses are normalized by direct algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-probabilities-nonnegative"),
                DeclarationHandle.Create(Prefix + "probabilities_nonneg"),
                H("Endpoint inequalities give nonnegative masses"),
                StatementSource.FromAuthor(Disp(NonnegativeFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The lower endpoint max(0, X+Y+Z−1) controls the first and last masses, while the upper endpoint min(X,Y) controls the two marginal differences. Z controls the middle mass."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-probabilities-positive"),
                DeclarationHandle.Create(Prefix + "probabilities_pos"),
                H("Strict endpoint inequalities give positive masses"),
                StatementSource.FromAuthor(Disp(PositiveFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict positivity follows under strict lower and upper endpoint inequalities together with 0 < Z."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-probabilities-recover"),
                DeclarationHandle.Create(Prefix + "probabilities_recover"),
                H("The marginal coordinates and overlap are recovered"),
                StatementSource.FromAuthor(Disp(RecoveryFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With zero-based Fin 5 indices p₀,…,p₄, the five masses recover X as p₁+p₄, Y as p₃+p₄, Z as p₂, and κ as p₄.")),
                    Paragraph(Text(
                        "This is a classical probability-coordinate bridge only. It does not assert native quantum amplitudes, a Born-rule realization, or a phase interpretation of κ."))),
                DescribeRole.Theorem))));

    private static Formula SumFormula()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var k = F.Id("kappa");
        return All("X", R(), All("Y", R(), All("Z", R(), All("kappa", R(),
            Equal(Call("sum", Call("probabilities", x, y, z, k)), D(1))))));
    }

    private static Formula NonnegativeFormula()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var k = F.Id("kappa");
        var assumptions = And(Le(D(0), z), And(
            Le(Call("lowerBound", x, y, z), k),
            Le(k, Call("upperBound", x, y))));
        return All("X", R(), All("Y", R(), All("Z", R(), All("kappa", R(),
            Implies(assumptions, All("i", Call("Fin", D(5)),
                Le(D(0), App(Call("probabilities", x, y, z, k), F.Id("i"))))))));
    }

    private static Formula PositiveFormula()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var k = F.Id("kappa");
        var assumptions = And(Lt(D(0), z), And(
            Lt(Call("lowerBound", x, y, z), k),
            Lt(k, Call("upperBound", x, y))));
        return All("X", R(), All("Y", R(), All("Z", R(), All("kappa", R(),
            Implies(assumptions, All("i", Call("Fin", D(5)),
                Lt(D(0), App(Call("probabilities", x, y, z, k), F.Id("i"))))))));
    }

    private static Formula RecoveryFormula()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var k = F.Id("kappa");
        var p = Call("probabilities", x, y, z, k);
        return All("X", R(), All("Y", R(), All("Z", R(), All("kappa", R(),
            And(Equal(Add(App(p, D(1)), App(p, D(4))), x), And(
                Equal(Add(App(p, D(3)), App(p, D(4))), y), And(
                    Equal(App(p, D(2)), z), Equal(App(p, D(4)), k))))))));
    }

    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
