using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ExactRateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/ExactRate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite counts turn escape reduction into positive unique capture.",
        H("Exact Escape Rates"),
        Blocks(
            Definition("escape-denominator", "escapeDenominator",
                H("Escape denominator"), DenominatorDefinition()),
            Theorem("escape-denominator-eq", "escapeDenominator_eq",
                H("Ordered-pair denominator formula"), DenominatorFormula()),
            Theorem("escape-denominator-pos", "escapeDenominator_pos",
                H("Nondegenerate denominator is positive"), DenominatorPositive()),
            Definition("escape-numerator", "escapeNumerator",
                H("Escape numerator"), NumeratorDefinition()),
            Definition("escape-rate", "escapeRate",
                H("Exact escape rate"), RateDefinition()),
            Definition("unique-capture-count", "uniqueCaptureCount",
                H("Unique capture count"), UniqueCountDefinition()),
            Definition("theorem-gain-rate", "theoremGainRate",
                H("Theorem gain rate"), GainDefinition()),
            Definition("lowers-escape", "LowersEscape",
                H("Strictly lowers escape"), LowersDefinition()),
            Theorem("escape-numerator-without-eq", "escapeNumerator_without_eq",
                H("Leave-one-out numerator decomposition"), NumeratorDecomposition()),
            Theorem("theorem-gain-rate-eq", "theoremGainRate_eq",
                H("Rate difference equals gain"), GainEquality()),
            Theorem("lowers-escape-iff-unique-capture-count-pos",
                "lowersEscape_iff_uniqueCaptureCount_pos",
                H("Strict reduction criterion"), PositiveCriterion()),
            Theorem("unique-capture-count-pos-iff-witness",
                "uniqueCaptureCount_pos_iff_witness",
                H("Unique capture witness criterion"), WitnessCriterion()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "This definition is computed from the finite arena and catalog kernels."))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The proof uses exact Finset cardinality and rational order transport."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arena() => F.Id("A");
    private static Formula Catalog() => F.Id("C");
    private static Formula Index() => F.Id("i");
    private static Formula Full() => Call("fullIndexSet", Catalog());
    private static Formula Without() => Call("without", Catalog(), Index());
    private static Formula Denominator() => Call("escapeDenominator", Arena());
    private static Formula Numerator(Formula selected) =>
        Call("escapeNumerator", Catalog(), selected);
    private static Formula Rate(Formula selected) => Call("escapeRate", Catalog(), selected);
    private static Formula UniqueCount() => Call("uniqueCaptureCount", Catalog(), Index());
    private static Formula Gain() => Call("theoremGainRate", Catalog(), Index());

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula DenominatorDefinition() => Seq(
        Denominator(), Sp, Eq, Sp,
        Call("card", Call("offDiagonalPairs", Call("State", Arena()))));

    private static Formula DenominatorFormula() => Seq(
        Denominator(), Sp, Eq, Sp, Call("card", Arena()), Sp, Times, Sp,
        Open, Call("card", Arena()), Sp, Minus, Sp, D(1), Close);

    private static Formula DenominatorPositive() => new Formula.Logic(
        Call("Nondegenerate", Arena()), FormulaLogicOperator.Implies,
        Seq(D(0), Sp, Lt, Sp, Denominator()));

    private static Formula NumeratorDefinition() => Seq(
        Numerator(F.Id("S")), Sp, Eq, Sp,
        Call("card", Call("escapePairs", Catalog(), F.Id("S"))));

    private static Formula RateDefinition() => Seq(
        Rate(F.Id("S")), Sp, Eq, Sp,
        Fraction(Numerator(F.Id("S")), Denominator()));

    private static Formula UniqueCountDefinition() => Seq(
        UniqueCount(), Sp, Eq, Sp,
        Call("card", Call("uniqueCapturePairs", Catalog(), Index())));

    private static Formula GainDefinition() => Seq(
        Gain(), Sp, Eq, Sp, Fraction(UniqueCount(), Denominator()));

    private static Formula LowersDefinition() => Seq(
        Call("LowersEscape", Catalog(), Index()), Sp, Leftrightarrow, Sp,
        Rate(Full()), Sp, Lt, Sp, Rate(Without()));

    private static Formula NumeratorDecomposition() => Seq(
        Numerator(Without()), Sp, Eq, Sp,
        Numerator(Full()), Sp, Plus, Sp, UniqueCount());

    private static Formula GainEquality() => new Formula.Logic(
        Call("Nondegenerate", Arena()), FormulaLogicOperator.Implies,
        Seq(Rate(Without()), Sp, Minus, Sp, Rate(Full()), Sp, Eq, Sp, Gain()));

    private static Formula PositiveCriterion() => new Formula.Logic(
        Call("Nondegenerate", Arena()), FormulaLogicOperator.Implies,
        Seq(Call("LowersEscape", Catalog(), Index()), Sp, Leftrightarrow, Sp,
            D(0), Sp, Lt, Sp, UniqueCount()));

    private static Formula WitnessCriterion() => Seq(
        D(0), Sp, Lt, Sp, UniqueCount(), Sp, Leftrightarrow, Sp,
        Exists, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        F.Id("x"), Sp, Neq, Sp, F.Id("y"), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("j"), Comma, Sp,
        F.Id("j"), Sp, Neq, Sp, Index(), Sp, Rightarrow, Sp,
        Call("agrees", Call("theoremAt", Catalog(), F.Id("j")),
            F.Id("x"), F.Id("y")), Close, Sp, Land, Sp, Neg,
        Call("agrees", Call("theoremAt", Catalog(), Index()),
            F.Id("x"), F.Id("y")));
}
