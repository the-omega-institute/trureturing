using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact renewal laws and the literal capped table.",
        H("Critical renewal sources and counted table"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-renewal-source-laws"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.source_laws"),
                H("Exact gap and equilibrium laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a natural r at least one, a positive real c, and s>0. The two shapes at every positive integer k are k^(2r-1) and k^(2r-1)+c k^(r-1). Their weights multiply these shapes by exp(-s k); both weights and densities are exactly zero at k=0. The normalizer is the sum over positive k. Every normalizer and positive-index density is strictly positive, both densities sum to one, and every fixed polynomial moment is finite.")),
                    Paragraph(Text("The density moments define mu=1+E K and beta=(E K^2+E K)/(2 mu). The tail S(u) sums the density over k>=u. Both S(0) and S(1) equal one, the sum of all tails is mu, and the equilibrium forward-wait mass is S(u)/mu for every natural u, including zero. This mass sums to one, its first moment is finite, and its mean is beta. The definitions gapLaw and waitLaw give the corresponding probability mass functions. The theorem also proves integrability and the actual measure integrals for every gap moment and for the equilibrium wait.")),
                    Paragraph(Text("For the equilibrium identities, a mass at gap k occurs once at each forward wait 0 through k. Summing these contributions gives (k+1) times its mass. Weighting each occurrence by its wait gives k(k+1)/2 times that same mass. Absolute summability follows from the polynomial geometric moments before interchanging the sums.")),
                    Paragraph(Text("Writing R_m(s) for the positive-index polynomial exponential sum and g=R_(r-1)/R_(2r-1), the exact pair identity is Z_1=(1+c g)Z_0. At every k>=1 the signed density difference is c[k^(r-1)-g k^(2r-1)] exp(-s k)/Z_1. The subtracted normalizer correction remains in this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-renewal-common-neighborhood"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.common_scalar_neighborhood"),
                H("One neighborhood for both source labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each fixed r>=1 and c>0 there are sStar in (0,1) and positive zMinus,zPlus,G,Cmu,Cbeta such that, whenever 0<s<sStar, both normalizers lie between zMinus/s^(2r) and zPlus/s^(2r), both cycle means are at most Cmu/s, and both 1+beta values are at most Cbeta/s. On the same neighborhood g<=G s^r. These constants are chosen before s and before every later phase cap.")),
                    Paragraph(Text("The polynomial geometric sum formula expresses the full natural-index sum using Stirling numbers of the second kind. Its zero-index term is removed explicitly, including when the exponent is zero. Clearing the denominator (1-exp(-s))^(m+1) leaves a finite polynomial whose value at exp(-s)=1 is m!. The derivative of 1-exp(-s) at zero is one, so s^(m+1)R_m(s) tends to m! from the positive side.")),
                    Paragraph(Text("For both shapes, every scaled raw moment has the same factorial limit as its leading monomial: the added term has a factor s^r and tends to zero. The source mean, equilibrium mean and g are ratios of these scaled quantities with positive limiting denominators. The finite collection of strict bounds for both labels has a common positive neighborhood. No moment estimate is an additional source assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-phase-coin-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.phase_coin_row"),
                H("The actual capped zero row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural cap J and phase z in Fin(J+1), mapping a Bernoulli coin with success probability 2^(-(z+1)) through Phase.step z gives exactly GeometricPhaseOccupation.finiteCappedRow J z. Live index z denotes source phase z+1. The last index J is dead; both fresh outcomes there have the same destination.")),
                    Paragraph(Text("The deterministic phase step stays on false and advances to min(z+1,J) on true. This includes J=0 and all finite phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-fresh-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.fresh_row"),
                H("Every bit row is a fresh coin transition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive natural H, natural J, immutable Tick J, counted state s and Boolean input bit x, the distribution of next(s,x,b), when b has coin(s,x), is exactly row(s,x).")),
                    Paragraph(Text("The complete state carrier is one wait, two Boolean labels, and every integer evidence value strictly between -H and H paired with Fin(J+1). Wait holds on zero and enters evidence zero and phase zero on one. Both label rows fix their label. Active zero rows use the capped phase row at fixed evidence. Active tick rows round by lower(z)+b and go directly through target. target emits label one at or above H, label zero at or below -H, and otherwise retains the new evidence at phase zero. The order of these cases is explicit. No pending phase is needed.")),
                    Paragraph(Text("The coin outcome is consumed by one transition. Its retained consequence is only the successor in the counted carrier. The table depends on no source label, time, history, gap length or external register. A tick following zero zeros is a fully specified row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-complete-gap-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.complete_gap_row"),
                H("The complete actual-gap row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive H, natural J, immutable Tick J, interior evidence e and natural duration k, wordLaw from (e,first) along exactly k zeros and one closing tick is the capped phase law at k, followed by that same phase's tick coin and target(e+lower(z)+b). The duration k=0 is included.")),
                    Paragraph(Text("wordLaw samples a new row coin for every consecutive input bit and applies the deterministic counted-state successor. No zero after phase death is omitted. Capped phase death preserves the evidence while zeros continue to be read."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-random-gap-row"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.random_gap_row"),
                H("Duration and mark remain joint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any probability mass function f on natural durations, the f-mixture of the literal complete-gap rows at an interior evidence e is the pushforward of pairLaw f t through (k,u) mapped to target(e+u).")),
                    Paragraph(Text("pairLaw first draws k with law f, then the capped phase after its k zeros, and finally the tick coin at that phase. Its second coordinate is the integer increment lower(z)+b. The increment is not assumed independent of its own duration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewaltable-full-state-count"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.full_state_count"),
                H("The entire listed carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural J and positive natural H, the cardinality of State H J is exactly 3+(2H-1)(J+1). All interior integer evidence values and all phases count; no reachability or positive-probability restriction is imposed.")),
                    Paragraph(Text("The three distinguished states are the wait and two internally emitted labels. The evidence interval has 2H-1 integers and the capped phase carrier has J+1 elements. The real choice H=ceil(A/delta) is a separate numerical specialization of this exact natural-H identity."))),
                DescribeRole.Theorem))));
}
