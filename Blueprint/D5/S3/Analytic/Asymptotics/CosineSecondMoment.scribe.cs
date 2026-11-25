using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class CosineSecondMomentDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Analytic/Asymptotics/CosineSecondMoment";
    private const string Digest = "A divergent second moment forces the normalized cosine defect to diverge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Divergence of the normalized cosine defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("divergent-cosine-second-moment"),
                DeclarationHandle.Create(Gid + ".tendsto_cosine_defect_div_sq_atTop"),
                H("A divergent second moment forces infinite positive curvature"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a and ω be real sequences indexed by ℕ. Assume a(n) ≥ 0 for "
                        + "all n, a is summable, and a(n)ω(n)² is not summable. Then "
                        + "(∑ₙ a(n)(1−cos(ω(n)h)))/h² tends to +∞ as h tends to zero "
                        + "through nonzero real values.")),
                    Paragraph(Text(
                        "Each defect summand is between zero and 2a(n). Given any real bound, "
                        + "choose a finite initial sum of a(n)ω(n)² that exceeds the bound "
                        + "after multiplication by 2/π². For h sufficiently small, all frequencies "
                        + "in that finite sum satisfy |ω(n)h| ≤ π. Then "
                        + "1−cos(ω(n)h) ≥ (2/π²)(ω(n)h)². Divide by h² and use the "
                        + "nonnegativity of every term outside the initial segment."))),
                DescribeRole.Theorem))));
}
