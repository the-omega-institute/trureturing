using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GaussianSignedLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed localization retains the entire envelope debit on an exact measurable complement.",
        H("Signed localization before absolute-value relaxation"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-localization-debit"),
            DeclarationHandle.Create("D5/S3/Analytic/GaussianSignedLocalization.signed_localization_debit"),
            H("A central upper bound with the full signed debit"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For real functions f,k,v,B and a measurable real set J, assume |k|<=v "
                    + "everywhere, 0<=B and f<=B on J, integrability of f*k and f*v on the "
                    + "whole line, and restricted integrability of B*v on J and |f|*v on its "
                    + "exact complement. Then integral(f*k) <= 2*integral_J(B*v) "
                    + "+2*integral_complement(|f|*v)-integral(f*v).")),
                Paragraph(Text(
                    "The proof first obtains 0<=k+v<=2*v. On J multiply f<=B by k+v; "
                    + "outside J multiply f<=|f| by k+v. The two indicator functions form an "
                    + "integrable pointwise upper bound after subtracting f*v. Integration "
                    + "retains that signed debit. Applying -x<=|x| recovers the original "
                    + "absolute-debit consequence without an unused weakening declaration.")),
                Paragraph(Text(
                    "OriginalPositiveUPeak.full_E_upper_of_central_bound actually applies this "
                    + "statement with f=Re(H), k=K, v=V, B=b and J=[4*m,28*m]. "
                    + "The original GaussianSignedLocalization.signed_localization_bound is "
                    + "therefore replaced by the stronger consumed form, rather than retained "
                    + "as an unconsumed parallel bound."))),
            DescribeRole.Theorem))));
}
