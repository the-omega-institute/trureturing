using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FixedTargetRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-target recovery and unattained stopping error", H("Fixed-target recovery and unattained stopping error"),
        Blocks(
            Describe.Lean(DescribeId.Create("past-information"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.pastInformation"),
                H("The raw nested past fields"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural-indexed filtration has field pastField(r) at radius r. Each chronological past word is a measurable projection of the next longer word, and all fields lie in the original joint process field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-map"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.fixedMAP"),
                H("Actual fixed-target MAP choices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every natural radius r and every Boolean word of length r, fixedMAP is the labelEquiv image of the original current_map_error cell-mass maximizer. Null words retain the same total selected choice."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("posterior"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.posterior"),
                H("Native actual posterior coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r, label a and original process realization z, posterior(r,a,z) is the real singleton mass at a of condDistrib(target,pastWord(r),J) evaluated at the actual past word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-map-recovery"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_map_recovery"),
                H("Same-law geometric MAP and Dirac limits"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On exactly the original J, every radius-r fixed-Q0 MAP error is at most ofReal((5/2)*rho^(r/2)), and these MAP estimates are almost surely eventually equal to Q0. For each of the six labels a, the actual target indicator has an almost-everywhere strongly measurable version in the supremum of the raw past fields, and its native posterior coordinate converges almost surely to that indicator. For every measurable seed space U and every probability measure nu, conditional expectations under the actual product-law completion and completed enlarged pastFiltration(nu,r) converge almost surely to the lifted target indicator. The seed is independent of the entire hidden/output process because the measure is J.prod(nu). The proof uses summable actual errors, Borel-Cantelli, measurable eventual-equality events and actual conditional-expectation martingale convergence. The target remains at time zero at every radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("admissible"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.admissible"),
                H("Almost-surely finite observable returns"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any measurable seed law nu, an arbitrary WithTop Nat-valued return map tau and arbitrary six-label returned map A are admissible when every finite return-label event is measurable in pastFiltration(nu,r), completed under J.prod(nu), and tau is finite almost surely. Nonterminating values remain in the domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("stopping-error-inf"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.stoppingErrorInf"),
                H("The actual stopped-error infimum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each measurable seed law nu, stoppingErrorInf is the ENNReal infimum of J.prod(nu)(A differs from the fixed Q0) over all return maps tau, all returned maps A, and proofs of admissible(nu,tau,A)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-zero-unattained-infimum"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_zero_unattained_infimum"),
                H("Zero error infimum without a finite zero-error return"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable seed space and probability nu, stoppingErrorInf(nu) is zero. Every admissible tau,A is a genuine stopping time for the actual completed enlarged filtration and has strictly positive actual product-law error. Every finite-radius actual MAP error under J is also strictly positive. The proof applies zero_error_iff_dirac_hitting to the actual native posterior vector on the completed common product measure. The native vectors are normalized and measurable, actual_completed_posterior supplies their conditional-expectation identities, and exact finite-past support excludes every finite Dirac hit. Deterministic finite MAP returns and the geometric bound approach zero error, so no radius-independent positive error floor follows."))), DescribeRole.Theorem))));
}
