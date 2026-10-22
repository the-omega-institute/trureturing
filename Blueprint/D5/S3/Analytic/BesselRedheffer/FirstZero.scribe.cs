using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class FirstZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity before the first zero and a radial trial-function estimate.",
        H("The first positive zero"), Blocks(
            Entry("bessel-positive-before-zero", "nbessel_pos_of_lt", "Positivity before the first zero",
                "For order nu greater than -1 and 0 less than or equal to x less than the first positive zero, the normalized series is positive at x. If it were nonpositive, continuity and its value one at zero would produce a positive zero no greater than x, contradicting the defining infimum."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/FirstZero." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
