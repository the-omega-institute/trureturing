using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RobinMeshFourierRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centered Robin samples recover literal zeta-zero multiplicity on a closed upper line.",
        H("Fourier recovery from canonical Robin records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-canonical-samples-fourier-recovery"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery."
                    + "actual_canonical_samples_fourier_recovery"),
                H("Recovery of the analytic multiplicity coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix w in ℂ with 1/2≤Re(w)<1 and assume Re(ρ)≤Re(w) for every nontrivial "
                        + "zeta zero ρ. Let N be a strictly increasing sequence in ℕ with N(0)>0 and "
                        + "N(k+1)/N(k)→1 in ℝ. Put y(k)=log(N(k)) and "
                        + "m(k)=strictInteger(firstLayerPrice(N(k)+1)). Write c(w)=2√2−2 if Re(w)=1/2 "
                        + "and c(w)=0 otherwise. For M>0 take the weighted average of the first M samples of "
                        + "(N(k)^(1−Re(w)) log(N(k)) robinLogMargin(m(k))−c(w)) exp(−i Im(w)y(k)), "
                        + "with weights y(k+1)−y(k) and divisor y(M)−y(0). As M→∞ this tends to "
                        + "−ord_w(ζ)/(w(1−w)) in ℂ, where ord_w(ζ) is analyticOrderNatAt riemannZeta w.")),
                    Paragraph(Text(
                        "The signed canonical sample asymptotic gives the negative of the complete "
                        + "normalized actual zero series up to an error tending to zero. The ratio-one "
                        + "condition supplies vanishing log gaps, and the closed-strip Fourier theorem "
                        + "selects the occurrences at w after demodulation. Each occurrence of ρ supplies "
                        + "1/(ρ(1−ρ)) to the zero series. The occurrence enumeration and the analytic-order "
                        + "identity count exactly ord_w(ζ) occurrences at w. If ζ(w)≠0, the limit is zero.")),
                    Paragraph(Text(
                        "The pointwise lower-bound criterion for an unattained upper abscissa remains "
                        + "open here."))),
                DescribeRole.Theorem))));
}
