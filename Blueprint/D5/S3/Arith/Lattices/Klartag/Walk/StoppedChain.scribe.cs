using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StoppedChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Stopped Chain"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate stopped chain to the stochastic ellipsoid construction.")),
            Node("claim-1", "tauOf", "tau Of",
                "The first exit before N. tauOf G N ω is the least k < N with ω ∉ G k, and N if there is none.", DescribeRole.Definition),
            Node("claim-3", "mem_of_lt_tauOf", "mem of lt tau Of",
                "Before the stopping time every event has held.", DescribeRole.Theorem),
            Node("claim-4", "tauOf_le_iff", "tau Of le iff",
                "{τ ≤ k} unfolds to a finite union of the failures at times ≤ k.", DescribeRole.Theorem),
            Node("claim-5", "isStoppingTime_tauOf", "is Stopping Time tau Of",
                "tauOf is a stopping time for any filtration measuring each G k at time k.", DescribeRole.Theorem),
            Node("claim-6", "stateGood", "state Good",
                "The ℱ k-measurable part of the good event at step k — exactly the three facts StateInvariant4.stateBounds_wired' consumes, and no more: the *earlier* per-step bounds, the accumulated bound at k, and the contact count at k.", DescribeRole.Definition),
            Node("claim-7", "stateGood_zero", "state Good zero",
                "The chain starts inside: gaussSum … 0 = 0 and C₀ = ∅.", DescribeRole.Theorem),
            Node("claim-8", "tau", "tau",
                "The stopping time: the first index at which the state conditions fail. It is a genuine stopping time for ℱ — stateGood k is ℱ k-measurable — and stateGood_zero makes it at least 1, so τ − 1 is always a *good* index. That is what the stopped state freezes at.", DescribeRole.Definition),
            Node("claim-10", "one_le_tau", "one le tau",
                "The chain never stops at 0.", DescribeRole.Theorem),
            Node("claim-11", "stateGood_of_lt_tau", "state Good of lt tau",
                "Every index strictly below the stopping time is good.", DescribeRole.Theorem),
            Node("claim-12", "stoppedState", "stopped State",
                "The stopped state A^τ_k := A_{min k (τ−1)}: frozen at the last index the state conditions covered. one_le_tau makes τ − 1 well defined and good.", DescribeRole.Definition),
            Node("claim-13", "stateBounds_stopped", "state Bounds stopped",
                "The bounds hold for the stopped state everywhere — no good event and no a.e. This is what makes the inverse state, its log-determinant and the chain error bounded, and so the eight integrability and measurability hypotheses of the drift theorem reachable.", DescribeRole.Theorem),
            Node("claim-14", "isStoppingTime_tau", "is Stopping Time tau",
                "τ is a stopping time for any filtration that measures the state conditions at their own index — which ChainSetup.filtration does, since Chain.measurable_chain makes the chain adapted and ξ j is ℱ (j+1)-measurable for j < k.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
