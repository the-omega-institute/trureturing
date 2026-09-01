using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenHawkingTemperatureNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenHawkingTemperatureNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden scale data alone do not determine Hawking temperature without " +
        "a physical-time normalization.",
        H("Golden Hawking Temperature Normalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-data-does-not-determine-hawking-temperature"),
            DeclarationHandle.Create(
                Prefix + "golden_data_does_not_determine_hawking_temperature"),
            H("Golden Data Do Not Determine Hawking Temperature"),
            StatementSource.FromAuthor(UnderdeterminationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Two positive affine-to-Killing-time conversions share the same golden " +
                    "scaling rate and regulator period but give different Hawking temperatures.")),
                Paragraph(Text(
                    "The witness isolates the missing time normalization; it does not claim " +
                    "that every pair of specifications has different temperatures."))),
            DescribeRole.Theorem))));

    private static Formula UnderdeterminationFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula specification = F.Id("GoldenTemperatureSpecification");
        Formula period = F.Id("goldenScalePeriod");
        Formula goldenData = Pair(period, period);
        Formula firstData = Call("goldenTemperatureData", a);
        Formula secondData = Call("goldenTemperatureData", b);
        Formula firstTemperature = Call("goldenHawkingTemperature", a);
        Formula secondTemperature = Call("goldenHawkingTemperature", b);
        Formula witness = Conjunction(
            Equality(firstData, goldenData),
            Conjunction(
                Equality(firstData, secondData),
                Inequality(firstTemperature, secondTemperature)));
        return Disp(Seq(
            Open, Exists, Sp, Typed(a, specification), Comma, Sp,
            Typed(b, specification), Comma, Sp, witness, Close, Dot));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);
    private static Formula Equality(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);
    private static Formula Inequality(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);
}
