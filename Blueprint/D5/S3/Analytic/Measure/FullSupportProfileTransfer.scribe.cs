using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Measure;

internal sealed class FullSupportProfileTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly Lipschitz nonnegative profiles with vanishing full-support integrals transfer to every finite measure.",
        H("Full-support integral transfer"), Blocks(
            Describe.Lean(DescribeId.Create("full-support-profile-transfer-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_of_full_support_integral"),
                H("Pointwise and finite-measure convergence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "On a pseudo-metric space with measurable open sets, let mu be locally finite and positive on every nonempty open set. Let continuous real g_j be nonnegative, uniformly bounded by a fixed M>=0 and Lipschitz with the same K>=0. Assume every g_j is mu-integrable and its mu-integral tends to zero. Then g_j(x) tends to zero at every x, and its integral against any measure nu of finite total mass tends to zero. A nonvanishing point and the uniform Lipschitz constant force a fixed positive lower integral on a finite open neighbourhood, contradicting the hypothesis. The second conclusion follows by dominated convergence. No compactness, optimizer, probability normalization or finiteness of mu is assumed. MaximalHockeyStickApproximate.actual_tests_full_support_transfer consumes the theorem with actual reverse-test gaps. This is a repository analytic supplier, rather than a claim of new literature priority."))),
                DescribeRole.Theorem))));
}
