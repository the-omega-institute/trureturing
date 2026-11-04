using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class LaguerreSevenHalfInverseMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact inverse Laguerre moment",
        H("Exact inverse Laguerre moment"),
        Blocks(
            Paragraph(Text("These supplier proofs are reused from commit 73c64f70. The underlying polynomial and moment definitions retain their OpenAI/math attribution and Apache-2.0 license. The argument evaluates polynomial Gamma integrals and their integration-by-parts recurrence; no boundary-value or completeness premise is assumed.")),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-inverse-integrable"),
                DeclarationHandle.Create(Owner + "centralPsi_integrable_inverse_square"),
                H("Every actual inverse moment is integrable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural mode n, x^(5/2) times psi_n(x)^2 is integrable on x>0. This supplies the near-origin absolute Mellin estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-inverse-value"),
                DeclarationHandle.Create(Owner + "centralPsi_integral_inverse_square"),
                H("The exact value is independent of the mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n, the same integral equals 4/7. This is an unbounded mode identity, derived from actual Laguerre orthogonality, the Gamma recurrence and the specified normalization. It is used by the uniform linear absolute Mellin bound; it is not a finite numerical certificate."))),
                DescribeRole.Theorem))));
}
