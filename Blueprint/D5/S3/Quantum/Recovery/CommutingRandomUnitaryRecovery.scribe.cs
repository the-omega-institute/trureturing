using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class CommutingRandomUnitaryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Optimal unitary recovery for diagonal random-unitary noise through dimension three.",
            "evidence-not-specified-by-formal-manifest"),
        H("The dimension bound for commuting quasi-inversion"),
        Blocks(
            Entry("li-tam", "extreme_rank_sq_le", "Li–Tam rank bound",
                "A complex correlation matrix is positive semidefinite with unit diagonal. Factor an extreme matrix "
                + "of rank r as V V* with V of full column rank. The real map H ↦ diag(V H V*) takes Hermitian "
                + "r by r matrices to a real d-dimensional space. If r² > d, a nonzero kernel element gives two "
                + "distinct feasible perturbations V(I ± tH)V* with the original matrix as their midpoint."),
            Entry("phase-maximizer", "phase_gram_max", "Rank-one maximizer in dimensions one to three",
                "The correlation matrices form a nonempty compact set. The maximizers of a linear functional "
                + "form an exposed face, so an extreme point of that face is extreme in the correlation set. "
                + "Li–Tam's inequality and the unit diagonal force rank one in positive dimension at most three."),
            Entry("mixture", "randomUnitaryChannel_action", "Channel action for arbitrary weights",
                "The Kraus operators are the unitaries scaled by the square roots of their weights. "
                + "The weights can vanish, and their sum is one."),
            Entry("score", "randomUnitary_score_kraus", "Canonical recovery score",
                "The normalized maximally entangled input is evaluated after the decoder is composed with the noise, "
                + "with identity on the reference. The canonical Kraus trace identity gives a weighted sum "
                + "of squared traces of decoder-branch products."),
            Entry("common-eigenbasis", "unitary_optimal_of_eigenbasis", "Recovery in a supplied common unitary basis",
                "Trace cyclicity transports the score to the common eigenbasis. Trace preservation bounds each "
                + "diagonal entry of the decoder Gram matrix by one. Adding a positive rank-one correction on "
                + "each coordinate fills its deficit and contributes a nonnegative amount to the objective. "
                + "A maximizing phase Gram matrix yields a diagonal unitary, which is carried back to the original basis."),
            Entry("diagonal-mixture", "diagonal_unitary_optimal", "Diagonal unitary optimum",
                "Every finite diagonal random-unitary mixture in dimensions one, two and three admits a single "
                + "diagonal unitary decoder attaining the score bound against all deterministic CPTP decoders."),
            Entry("simultaneous-diagonalization", "simultaneous_unitary_eigenbasis", "Simultaneous unitary diagonalization",
                "Unitary inverses equal adjoints, so the real and imaginary parts of the branches form a commuting "
                + "family of self-adjoint operators. Their orthogonal joint eigenspaces furnish a common unitary eigenbasis."),
            Entry("commuting-mixture", "commuting_unitary_optimal", "Unitary optimum for pairwise commuting branches",
                "For every finite probability-weighted mixture of pairwise commuting unitary conjugations on a "
                + "nonzero code of dimension at most three, one unitary decoder attains the canonical entanglement "
                + "fidelity against all deterministic CPTP decoders. The separate dimension-four example attains "
                + "1/4 + √3/6 by a CPTP decoder and gives a strictly smaller score for every unitary decoder."))));

    private static DocumentBlock Entry(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
