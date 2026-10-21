using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kummer series and ratios with shifted upper parameters.",
        H("The upper parameter ratio"), Blocks(
            Entry("kummer-coefficient", "kummerCoeff", "The series coefficient",
                "For real s and c and a natural n, the coefficient is the rising factorial of s of order n divided by the rising factorial of c of order n and by n factorial."),
            Entry("kummer-function", "kummer", "Kummer's function",
                "The function M(s;c;x) is the sum over all natural n of the coefficient times x to the power n."),
            Entry("kummer-ratio", "ratio", "The shifted upper parameter ratio",
                "The ratio is M(b+delta;c;x) M(a;c;x) divided by M(a+delta;c;x) M(b;c;x)."),
            Entry("kummer-claim", "claim", "Monotonicity and exact ranges",
                "For c and delta positive and 0<a<b, the ratio is strictly decreasing on the positive ray and has image (Gamma(a+delta) Gamma(b)/(Gamma(b+delta) Gamma(a)),1). For a<b<c-delta, it is strictly increasing on the negative ray and has image (Gamma(c-a-delta) Gamma(c-b)/(Gamma(c-b-delta) Gamma(c-a)),1)."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
