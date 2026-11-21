using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RobinMeshAttainedSignsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/RobinMeshAttainedSigns";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An attained off-line zeta abscissa forces both signs on every ratio-one canonical Robin mesh.",
        H("Two-sided Robin excursions on a prescribed mesh"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-attained-canonical-critical-subsequences"),
                DeclarationHandle.Create(Gid + ".actual_attained_canonical_critical_subsequences"),
                H("Opposite signed excursions at the critical exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose a nontrivial zeta zero ρ attains the zero abscissa Θ and satisfies "
                        + "Re(ρ)>1/2. Let N be any strictly increasing sequence of natural numbers "
                        + "with N(0)>0 and N(k+1)/N(k)→1 in ℝ. Define the canonical integer "
                        + "m(k)=strictInteger(firstLayerPrice(N(k)+1)) and the normalized margin "
                        + "R(α,k)=N(k)^α log(N(k)) robinLogMargin(m(k)). There exist c>0 and two "
                        + "strictly increasing index sequences i₊ and i₋ such that "
                        + "R(1−Θ,i₊(j))>c and R(1−Θ,i₋(j))<−c for every j.")),
                    Paragraph(Text(
                        "Fourier recovery at the real point Θ gives a zero gap-weighted mean "
                        + "because ζ(Θ) is nonzero. Recovery at ρ gives the nonzero limit "
                        + "L=−ord(ζ,ρ)/(ρ(1−ρ)) after multiplication by exp(−i Im(ρ) log(N(k))), "
                        + "where ord(ζ,ρ) is the analytic zero order at ρ. "
                        + "The twist has norm one. The two-sided zero-mean lemma with c=‖L‖/4 "
                        + "gives arbitrarily late excursions of each sign, from which increasing "
                        + "index sequences are extracted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-attained-canonical-divergent-subsequences"),
                DeclarationHandle.Create(Gid + ".actual_attained_canonical_divergent_subsequences"),
                H("Divergence to opposite infinities above the critical exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same hypotheses on ρ and N, for each real α>1−Θ there are "
                        + "strictly increasing index sequences i₊ and i₋ such that "
                        + "R(α,i₊(j))→+∞ and R(α,i₋(j))→−∞.")),
                    Paragraph(Text(
                        "Use the two critical index sequences. Along each sequence the factor "
                        + "N(k)^(α−(1−Θ)) tends to +∞. Multiplying the critical sign bounds by "
                        + "this positive factor gives a lower bound tending to +∞ on i₊ and an "
                        + "upper bound tending to −∞ on i₋."))),
                DescribeRole.Theorem))));
}
