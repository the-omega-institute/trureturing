using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class PrimeGoldenScaleCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime logarithmic lengths admit a golden scale coordinate without yet defining a dynamical wormhole.",
        H("Prime–Golden Scale Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-powers-advance-linearly-in-golden-scale"),
                DeclarationHandle.Create(
                    Prefix + "prime_power_golden_scale_coordinate"),
                H("Prime powers advance linearly in golden scale"),
                StatementSource.FromAuthor(PrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A positive scale is mapped to its logarithm divided by the golden scale "
                            + "period. Applying this coordinate to a prime gives a typed arithmetic "
                            + "scale address.")),
                    Paragraph(Text(
                        "Prime powers are linear in this lifted coordinate because logarithms turn "
                            + "multiplicative powers into additive multiples.")),
                    Paragraph(Text(
                        "The owner deliberately makes no semiconjugacy claim: a prime-to-golden "
                            + "wormhole still requires an explicit prime dynamics and a commuting "
                            + "square."))),
                DescribeRole.Theorem))));

    private static Formula PrimeFormula() => Disp(Seq(
        Call("goldenScaleCoordinate", Call("pow", F.Id("p"), F.Id("n"))),
        Sp, Eq, Sp, F.Id("n"), Sp,
        Call("primeGoldenScaleCoordinate", F.Id("p"))));
}
