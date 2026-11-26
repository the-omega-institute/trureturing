using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NonperturbativePhaseResummationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-coupling absolute convergence versus perturbative cubic harmonic divergence in phase-oscillating mode sums.",
        H("Nonperturbative phase resummation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonperturbative-phase-mode-term"),
                DeclarationHandle.Create(Prefix + "modeTerm"),
                H("Radial mode term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("The k-th mode term (g² / 2) exp(-2 i (k + 1) g) / (k + 1)² at coupling parameter g = 1/s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonperturbative-phase-partial-sum"),
                DeclarationHandle.Create(Prefix + "partialPhaseSum"),
                H("N-mode partial phase sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Finite cutoff sum F_N(g) = ∑_{k < N} modeTerm g k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonperturbative-phase-summable-and-bound"),
                DeclarationHandle.Create(Prefix + "summable_and_norm_le_modeTerm"),
                H("Finite-coupling absolute convergence and uniform quadratic bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Formalizes the finite-coupling convergence of Chandrasekaran (arXiv:2611.34924v1, Section 4.4, Eq. 4.33): "
                    + "for every real coupling g, the infinite mode series converges absolutely and its sum has norm at most g²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonperturbative-phase-cubic-deriv-zero"),
                DeclarationHandle.Create(Prefix + "iteratedDeriv_three_partialPhaseSum_zero"),
                H("Exact cubic perturbative coefficient at zero coupling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Formalizes Eq. 4.34: for every finite mode cutoff N, (1/6) iteratedDeriv 3 (partialPhaseSum N) 0 "
                    + "equals -i times the N-th harmonic number H_N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonperturbative-phase-cubic-divergence"),
                DeclarationHandle.Create(Prefix + "tendsto_neg_im_cubic_coeff_atTop"),
                H("Harmonic divergence of the cubic perturbative coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("As N → ∞, the negative imaginary part of the cubic coefficient at g = 0 diverges to +∞, "
                    + "witnessing the failure of the UV limit and zero-coupling expansion to commute."))),
                DescribeRole.Theorem))));
}
