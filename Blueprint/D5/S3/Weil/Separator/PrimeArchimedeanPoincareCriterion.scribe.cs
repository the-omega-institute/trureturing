using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class PrimeArchimedeanPoincareCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative to supplied zero data, RH is equivalent to the Prime-Archimedean "
            + "Poincare inequality at every support radius and at some support radius.",
        H("Prime-Archimedean Poincare Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rh-iff-prime-archimedean-poincare"),
                DeclarationHandle.Create(Prefix + "rh_iff_primeArchimedeanPoincare"),
                H("RH is equivalent to every-radius Prime-Archimedean Poincare"),
                StatementSource.FromAuthor(EveryRadiusFormula()),
                AssessedProvenance.FromRepo(),
                ExplanatoryBlocks(),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-exists-support-radius-prime-archimedean-poincare"),
                DeclarationHandle.Create(
                    Prefix + "rh_iff_exists_supportRadius_primeArchimedeanPoincare"),
                H("RH is equivalent to existential-radius Prime-Archimedean Poincare"),
                StatementSource.FromAuthor(ExistsRadiusFormula()),
                AssessedProvenance.FromRepo(),
                ExplanatoryBlocks(),
                DescribeRole.Theorem)),
        []));

    private static BlockSequence ExplanatoryBlocks() => Blocks(
        Paragraph(Text(
            "The energy decomposition is the frozen theorem PrimeArchimedeanEnergyIdentity "
                + "proved by another driver and is only bound here; no part of that identity "
                + "is reproved.")),
        Paragraph(Text(
            "Both criteria are relative to a ZeroData only. Existence of ZeroData is not "
                + "asserted, M1-b remains open, and these equivalences are not a proof of RH.")),
        Paragraph(Text(
            "The quantified test functions are this repository's WeilTestFunction. The "
                + "support radius L is any real satisfying tsupport f subset [-L,L]. The "
                + "existential-radius criterion records that, through the frozen identity, "
                + "the inequality's truth is independent of which valid radius is chosen.")),
        Paragraph(Text(
            "The left side is the coherent prime mass minus the Archimedean constant, "
                + "multiplied by the L2 mass. The right side is twice the squared boundary "
                + "readout plus the Archimedean and arithmetic jump energies.")));

    private static Formula EveryRadiusFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula criterion = ForAll(
            [Bound("f", F.Id("WeilTestFunction")), Bound("L", Reals())],
            Implies(SupportCondition(test, scale), PoincareInequality(test, scale)));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Iff(RiemannHypothesis(), criterion)));
    }

    private static Formula ExistsRadiusFormula()
    {
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula criterion = ForAll(
            [Bound("f", F.Id("WeilTestFunction"))],
            Exists(
                [Bound("L", Reals())],
                And(SupportCondition(test, scale), PoincareInequality(test, scale))));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Iff(RiemannHypothesis(), criterion)));
    }

    private static Formula SupportCondition(Formula test, Formula scale) =>
        new Formula.Relation(
            Call("tsupport", test),
            FormulaRelationOperator.SubsetOf,
            Seq(OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket));

    private static Formula PoincareInequality(Formula test, Formula scale)
    {
        Formula variable = F.Id("x");
        Formula boundaryReadout = Seq(
            Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            Call("exp", Seq(Frac, Grp(variable), Grp(D(2)))), Sp,
            Call("f", variable), Sp, F.Id("d"), variable);
        Formula boundaryEnergy = Seq(
            D(2), Sp, Lvert, boundaryReadout, Rvert, Caret, Grp(D(2)));
        Formula totalEnergy = Add(
            Add(boundaryEnergy, Call("archimedeanJumpEnergy", test)),
            Call("arithmeticJumpEnergy", scale, test));
        Formula thresholdCoefficient = Subtract(
            Multiply(D(2), Call("totalPrimeWeight", scale)),
            Seq(Operatorname, Grp(F.Id("archimedeanConstant"))));
        Formula threshold = Multiply(thresholdCoefficient, Call("l2Mass", test));

        return LessOrEqual(threshold, totalEnergy);
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
