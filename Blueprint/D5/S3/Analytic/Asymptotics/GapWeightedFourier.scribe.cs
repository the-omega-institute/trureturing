using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class GapWeightedFourierDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Analytic/Asymptotics/GapWeightedFourier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, "Gap-weighted averages recover coefficients on a closed upper line.",
            "evidence-not-specified-by-formal-manifest"),
        H("Fourier recovery on a mesh with vanishing gaps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tendsto-average-closed-strip-series"),
                DeclarationHandle.Create(Gid + ".tendsto_average_closed_strip_series"),
                H("Coefficient recovery on a closed upper line"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let y be a strictly increasing real sequence tending to +∞ with gaps "
                        + "d(k)=y(k+1)−y(k) tending to zero. For M>0 the gap-weighted average of s "
                        + "is A(M)=∑_{k<M} d(k)s(k)/(y(M)−y(0)). Let a(i) and z(i) be complex families "
                        + "on an arbitrary index type with summable coefficient norms. Fix w in ℂ with "
                        + "Re(z(i))≤Re(w) for every i. If e(k) tends to zero in ℂ and "
                        + "s(k)=∑ᵢ a(i) exp(y(k)(z(i)−w))+e(k), then A(M) tends to the sum of a(i) "
                        + "over exactly the indices with z(i)=w.")),
                    Paragraph(Text(
                        "The modes strictly below Re(w) decay. On the bounding line each nonzero "
                        + "frequency averages to zero by comparison with its integral over the "
                        + "mesh intervals. The mode at w is constant. The exponential factors are "
                        + "bounded by one once y is nonnegative, so absolute summability permits "
                        + "passage to the limit in the series. The average of the null error tends to zero."))),
                DescribeRole.Theorem))));
}
