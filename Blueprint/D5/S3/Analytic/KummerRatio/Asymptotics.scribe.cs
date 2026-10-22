using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class AsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading positive-real asymptotic of the Kummer series.",
        H("Gamma-normalized Kummer asymptotics"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-positive-endpoint-asymptotic"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Asymptotics.tendsto_kummer_atTop"),
                H("The exact leading coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive upper parameter s and positive lower parameter c, the quantity exp(-x) x^(c-s) M(s;c;x) tends to Gamma(c)/Gamma(s) as x tends to positive infinity.")),
                    Paragraph(Text("When s is less than c, the beta integral represents the Kummer series. The normalized integral concentrates at the right endpoint, and its limit is Gamma(c-s). Multiplication by the beta normalization gives the stated coefficient.")),
                    Paragraph(Text("For all other positive parameters, the contiguous relation expresses the normalized function as the sum of two normalized functions with a larger lower parameter. The first is multiplied by 1/x and tends to zero. The coefficient of the second reduces to Gamma(c)/Gamma(s) by the Gamma recurrence. Induction on a natural upper bound for s-c reaches the integral case."))),
                DescribeRole.Theorem))));
}
