using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenScaleCircleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden logarithmic scale converts positive multiplication into additive shell translation.",
        H("Golden Scale Circle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-scale-multiplicative-additivity"),
                DeclarationHandle.Create(Prefix + "golden_scale_coordinate_mul"),
                H("Multiplication becomes addition"),
                StatementSource.FromAuthor(Disp(Call("goldenScaleCoordinateMul", F.Id("x"), F.Id("y")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive scales, logarithmic normalization by two log phi converts multiplication into addition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-unit-is-one-shell"),
                DeclarationHandle.Create(Prefix + "golden_scale_coordinate_phi_sq_mul"),
                H("Multiplication by phi squared advances one shell"),
                StatementSource.FromAuthor(Disp(Call("goldenShellStep", F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The orientation-preserving golden unit phi squared has logarithmic length exactly one golden period."))),
                DescribeRole.Theorem))));
}
