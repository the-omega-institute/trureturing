using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class PrimeGoldenScaleCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime logarithmic lengths admit a golden scale coordinate.",
        H("Prime Golden Scale Coordinate"),
        Blocks(
            Theorem(
                "prime-golden-scale-coordinate-pos",
                "prime_golden_scale_coordinate_pos",
                PrimeGoldenScaleCoordinatePosFormula(),
                "Prime Golden Scale Coordinate pos",
                "Every prime has a positive golden scale coordinate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "prime-power-golden-scale-coordinate",
                "prime_power_golden_scale_coordinate",
                PrimePowerGoldenScaleCoordinateFormula(),
                "Prime Power Golden Scale Coordinate",
                "Prime powers advance linearly in the lifted golden scale coordinate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "prime-one-golden-scale-coordinate",
                "prime_one_golden_scale_coordinate",
                PrimeOneGoldenScaleCoordinateFormula(),
                "Prime One Golden Scale Coordinate",
                "The coordinate of the first power is the prime coordinate itself.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula PrimeGoldenScaleCoordinatePosFormula() => Statement(
    [Typed(Seq(F.Id("prime")), Seq(Mathbb, Grp(F.Id("N")), Dot, F.Id("Primes")))],
        [],
        [],
        Seq(D(0), Sp, Lt, Sp, F.Id("primeGoldenScaleCoordinate"), Sp, F.Id("prime")));

private static Formula PrimePowerGoldenScaleCoordinateFormula() => Statement(
    [Typed(Seq(F.Id("prime")), Seq(Mathbb, Grp(F.Id("N")), Dot, F.Id("Primes"))), Typed(Seq(F.Id("exponent")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [],
        Seq(F.Id("goldenScaleCoordinate"), Sp, Open, Open, F.Id("prime"), Dot, D(1), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Close, Sp, Caret, Grp(F.Id("exponent")), Close, Sp, Eq, Sp, F.Id("exponent"), Sp, Times, Sp, F.Id("primeGoldenScaleCoordinate"), Sp, F.Id("prime")));

private static Formula PrimeOneGoldenScaleCoordinateFormula() => Statement(
    [Typed(Seq(F.Id("prime")), Seq(Mathbb, Grp(F.Id("N")), Dot, F.Id("Primes")))],
        [],
        [],
        Seq(F.Id("goldenScaleCoordinate"), Sp, Open, F.Id("prime"), Dot, D(1), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Close, Sp, Eq, Sp, F.Id("primeGoldenScaleCoordinate"), Sp, F.Id("prime")));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
