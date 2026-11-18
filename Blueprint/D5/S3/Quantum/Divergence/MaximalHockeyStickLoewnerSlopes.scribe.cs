using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickLoewnerSlopesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");
    private static readonly LibraryNoteRef Matsumoto =
        LibraryNoteRef.Create("D5/L/Divergence/matsumoto2018newquantumfdivergence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual optimal PSD overlaps give a finite Loewner-secant criterion, necessary for original-L1 equality and sufficient for every finite interpolation problem.",
        H("Optimal overlaps and finite Loewner slopes"), Blocks(
            Paragraph(Text("Let n be any finite type, including the empty type, and let A,B be arbitrary positive semidefinite complex n by n matrices. There is no trace normalization or invertibility assumption. O(t) is the supremum of Re Tr(X) over 0<=X<=A and X<=tB. A private uniqueness argument concerns these constrained PSD trace maximizers, rather than the unconstrained Hermitian lower-bound problem. It uses the existing subunital quadratic Jensen theorem: the square of half the difference of two maximizers can be added to their midpoint after positive scaling. Optimality forces its trace to vanish, so the two matrices coincide. Finite-dimensional compactness then turns convergence of feasible traces into convergence to this unique optimum.")),
            Node("optimalOverlap", "The actual matrix optimum",
                "For t>=0, optimalOverlap A B hA hB t chooses an attained maximum from positiveOverlaps A (t B); for negative t its value is zero and is unused. The optimizer is uniquely determined by the PSD constrained problem. It is not a postulated profile or a chosen reverse-test optimizer.", false),
            Node("optimalOverlap_spec", "Feasibility and optimal trace",
                "At every nonnegative t the chosen matrix lies between zero and each of A,tB, and its real trace is overlapValue A (tB). These facts supply the matrix endpoints of every interpolation tuple.", true),
            Node("optimalOverlap_zero", "The virtual initial knot",
                "The actual optimum at zero is zero, also for singular pairs and empty matrix dimension. Zero is used as an initial interpolation knot; curvature is a measure on the strictly positive threshold space and has no zero or infinity point.", true),
            Node("secant", "Matrix secants",
                "For a matrix function X, secant X s t is (t-s)^(-1) times (X(t)-X(s)). Each ordered pair of distinct tuple knots therefore defines an actual matrix, compared in Loewner order.", false),
            Node("FiniteLoewnerSlopes", "The exact arbitrary-support condition",
                "For every natural m and every strictly increasing tuple t:Fin(m+1)->R with t(0)=0 and every positive node belonging to K, form D_i=(X(t_(i+1))-X(t_i))/(t_(i+1)-t_i), where X is optimalOverlap. Require 0<=D_i<=B for every i and Antitone D. These are matrix inequalities, not inequalities of traces. The tuple with m=0 is included. K may be empty, finite, disconnected or unbounded; the classifier uses the actual Stieltjes support of the generator.", false),
            Node("trace_prepared", "Trace of an actual prepared overlap",
                "For every actual finite ReverseTest R and every real t, Re Tr(R.preparedOverlap t) is the sum of min(R.p_i,t R.q_i). The component trace identities give this formula, which expresses the tail hinge profiles in terms of prepared overlaps.", true),
            Node("gap_eq_overlap_trace", "The actual gap is an overlap deficit",
                "At each positive threshold, gap R t equals O(t)-Re Tr(R.preparedOverlap t). Both original equality necessity and the dominated-convergence sufficiency proof consume this identity.", true),
            Node("prepared_secant_bounds", "Bounds for prepared slopes",
                "For any finite actual reverse test and s<t, its prepared-overlap secant is PSD and bounded above by B. The scalar min(p,tq) secants lie in [0,q], and the same density states prepare B. No optimum or full-support assumption is needed.", true),
            Node("prepared_secant_antitone", "Ordered prepared secants",
                "For r<s<=t<v, the prepared secant over [t,v] is bounded above in Loewner order by the secant over [r,s]. This follows from the scalar concavity of min(p,tq), with the common actual preparation retained.", true),
            Node("prepared_overlap_tendsto_of_gap", "From vanishing gap to the actual optimum",
                "For any sequence of actual finite tests with gap tending to zero at a fixed positive t, their prepared overlap matrices converge to optimalOverlap(t). Compactness is only in the finite-dimensional feasible matrix set. Uniqueness identifies every limiting optimizer; no test attaining the general convex infimum is assumed.", true),
            Node("original_eq_implies_finiteLoewnerSlopes", "Necessity for the original whole-complex-L1 values",
                "For any real f convex on Ioi 0 and any real c with originalL1Value hf A B=c, equality originalL1Value=originalHockeyValue implies FiniteLoewnerSlopes on the actual curvature support. The source universe u is arbitrary and independent of the matrix universe. originalL1Value ranges over all sigma-finite sources and positive complex-linear TP maps defined on their entire complex L1 spaces. The original operational hockey infima are identified by the previously proved source bridges. Finite-cost near-minimizers have nonnegative uniformly Lipschitz gaps whose curvature integrals tend to zero. The analytic support transfer gives pointwise vanishing at each actual support knot; optimizer convergence and closed Loewner order pass the finite prepared-slope conditions to the actual optimal-overlap slopes. Full curvature support, normalization, faithfulness and a nonempty output type are unnecessary.", true),
            Node("hockey_eq_trace_sub", "Positive hockey as trace minus overlap",
                "For each actual finite test and real threshold, its positive hockey sum equals Tr(A)-Re Tr(preparedOverlap). This gives the positive branch of the test kernel used in the dominated-convergence argument. A general closed-perspective cost is represented by a curvature integral of test kernels.", true),
            Node("finite_test_interpolating_slopes", "Finite interpolation by explicit PSD blocks",
                "Given a finite strictly increasing tuple starting at zero, actual optimal feasible matrices X_j with X_0=0, and an antitone extended slope tuple d ending at zero with d_0<=B and (t_(i+1)-t_i)d_i=X_(i+1)-X_i, the proof constructs an actual finite ReverseTest with preparedOverlap(t_j)=X_j for every j. Its PSD blocks are the slope differences d_i-d_(i+1), the lower residual B-d_0 and the upper residual A-X_last. Summation by parts proves both original matrix marginals and every interpolation identity. Empty output dimension uses the empty alphabet, and zero blocks use the existing weighted-component convention.", true),
            Node("finiteLoewnerSlopes_realizes_knots", "Every compatible finite tuple is realizable",
                "FiniteLoewnerSlopes A B hA hB K supplies an actual finite test interpolating optimalOverlap at every knot of any specified tuple in K with virtual initial zero. Appending a final zero slope supplies the preceding block construction. The alphabet may depend on the tuple. This gives neither a uniform alphabet size nor one finite test simultaneously optimal on an infinite support.", true),
            Paragraph(Text("Attribution: Hiai, Mosonyi and Tomamichel, arXiv:2607.08760v1, Proposition V.1, supply the actual positive-overlap hockey formulas and one-threshold three-component construction. Their final equality question motivates this extension. Matsumoto, arXiv:1311.4722v4, p. 8, Lemma 4.1, already supplies one-cost finite-source compression. The previous source-class equivalence and original-L1 operational profile identification are reused at their exact scopes. The finite interpolation and arbitrary-support classification are repository derivations; worldwide novelty remains unverified."))
        )));

    private static DocumentBlock Node(string name, string heading, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-loewner-slopes-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source, Matsumoto), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
