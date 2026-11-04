using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class FiniteRankClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinal rank classification for the actual completed channel.",
        H("Cardinal rank classification for the actual completed channel"),
        Blocks(Describe.Lean(DescribeId.Create("actual-fock-rank-three-classification"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification.actual_rank_three_iff_profile"),
            H("Cardinal rank classification for the actual completed channel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every nonzero a in lp(Natural -> Complex,2), the actual output of the balanced two-photon pure attenuator has Cardinal Module.rank of its operator range at least three. Its rank equals three exactly when the Bargmann transform of a is c*exp(alpha*z) or c*exp(alpha*z)*(z-beta)^2, for arbitrary complex parameters with c nonzero.")),
                Paragraph(Text("Finite Cardinal output rank is equivalent to an exponential-polynomial Bargmann transform for every completed input, including zero. Thus a transform outside that class has no natural bound on its actual output range dimension. Infinite-dimensional ranges are never replaced by finrank.")),
                Paragraph(Text("The actual point-mass ProbabilityVector reduces the existing double-index pure output ensemble to purePartialTrace of the existing beam splitter output. The completed kernel formula, exact-count rescaling, Hilbert rank/separation equivalence and entire scalar classification then prove the statements. The nonzero lower bound also proves exact attainment for both equality profiles.")),
                Paragraph(Text("This independent rank classification does not settle the parent all-density entropy problem, the spectral entropy and mixed-ensemble joins, the remaining E1/M0/P1/M3 obligations, a universal elementary-symmetric lower bound, or the all-n/all-eta conjecture. Those parent obligations remain open."))),
            DescribeRole.Theorem))));
}

