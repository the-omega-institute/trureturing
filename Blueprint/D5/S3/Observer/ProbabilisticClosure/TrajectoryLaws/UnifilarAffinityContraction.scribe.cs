using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class UnifilarAffinityContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One distinguishing length and killed-pair contraction", H("One distinguishing length and killed-pair contraction"),
        Blocks(
            Describe.Lean(DescribeId.Create("word-total"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.word_total"),
                H("Normalization of every finite unifilar word law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite state type, real Boolean symbol masses p summing to one at each state, arbitrary successor map delta, natural length n and initial state a, the sum of wordMass(p,delta,n,a,w) over every word w is one. No positivity premise is needed for this algebraic identity. TwelveStatePresentation consumes the unchanged original inductive supplier in its actual length-two affinity proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-block"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.matrix_block"),
                H("A specified strict block bound controls all powers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite matrix B with nonnegative entries and row sums at most one, positive natural block length ell, nonnegative real rho, and every ell-th power row sum at most rho, the n-th power row sum at every row is at most rho^(n/ell), for every natural n. This is the unchanged original supplier used by finite_distinguishing_contraction and by TwelveStateTail at ell=2 with the explicit actual affinity constant."))), DescribeRole.Theorem),
            Paragraph(Text("Let S be any finite state set. The nonnegative real symbol masses p(a,x) sum to one over both Boolean symbols at every a. The same successor map delta:S times Bool to S generates wordMass and endpoint from UnifilarPairSurvival. No stationarity, communication, positivity of symbols, aperiodicity or synchronization assumption is present. An empty pair set is allowed.")),
            Paragraph(Text("The finite distinguishing hypothesis says that for every distinct a,b there exists a natural length n at which their entire wordMass functions differ. This module proves the common finite-length consequence; OriginalUnifilarQuotient discharges that hypothesis for the actual complete-future-law quotient of the selected original presentation. It is an intermediate supplier, not an independently selected probability model.")),
            Describe.Lean(DescribeId.Create("word-nonneg"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.word_nonneg"),
                H("Nonnegative masses along the same trajectory"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every state type S, p, delta and nonnegative p, natural n, state a and Boolean word of length n, wordMass(p,delta,n,a,w) is nonnegative. The proof inducts over this same word. OriginalUnifilarQuotient uses it inside the actual endpoint/MAP estimate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-distinguishing-contraction"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.finite_distinguishing_contraction"),
                H("A common strict block controls every killed-pair power"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such p and delta with pairwise distinct finite-word laws, there exist a natural ell greater than zero and a real rho with 0 <= rho < 1. At this same ell, every distinct pair has different length-ell wordMass functions and Bhattacharyya affinity at most rho. For every natural n and ordered distinct pair s, the row sum of pairMatrix(p,delta) raised to n at s is at most rho raised to the natural quotient n/ell.")),
                    Paragraph(Text("Word concatenation factors into prefix and suffix along the same deterministic endpoint. Summing all suffixes gives the prefix mass because every future word distribution is normalized. Select a distinguishing length for each of the finitely many pairs and take their maximum together with one. If two distributions agreed at that length, summing their suffixes would contradict the chosen shorter distinction. This proves a common length without a computable or efficient bound.")),
                    Paragraph(Text("Apply the existing normalized Bhattacharyya upper bound and total-variation square inequality. A distinct pair has nonzero total variation by Metric.total_variation_eq_zero_iff, so affinity is strictly below one. The maximum over the finite pair affinities, together with zero for the empty-pair boundary, is an actual common rho below one. No estimated numerical constant is used.")),
                    Paragraph(Text("pairMatrix_action and normalization bound each pair-matrix row by one. The exact existing pair_survival_word_affinity identifies its ell-th power row sum with affinity restricted to nonmerged words; this is at most the full distinguished-word affinity. A nonnegative matrix with row sums at most one and an ell-block row bound rho has n-th-power row sums at most rho^(n/ell): split off ell by strong induction, bound the short remainder by one, and multiply nonnegative rows. Natural division is exactly floor(n/ell). The proof keeps n=0 and zero symbol weights. If rho=0, zero to the zeroth power is one and all powers at n>=ell have zero row sum."))), DescribeRole.Theorem))));
}
