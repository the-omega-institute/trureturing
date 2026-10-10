using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class SimplexDeletionMinimaxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/MetricGeometry/SimplexDeletionMinimax.";
    private static readonly LibraryNoteRef RelativeCenters =
        LibraryNoteRef.Create("D5/L/Geometry/amir1985jung");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common probability centers determine the sharp deterministic risk of noisy deletion observations.",
        H("Simplex centers and deletion minimax risk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplex-common-center"),
                DeclarationHandle.Create(Prefix + "simplex_common_center"),
                H("One probability center for every possible source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(RelativeCenters),
                Blocks(
                    Paragraph(Text(
                        "For every integer m at least two, let K be a nonempty compact set of real "
                        + "vectors with m nonnegative coordinates summing to one. Let w be any "
                        + "nonnegative real number such that every coordinate difference between "
                        + "every pair of points of K has absolute value at most w. There exists one "
                        + "vector q with nonnegative coordinates summing to one such that, for every "
                        + "p in K and every coordinate i, the absolute difference between p(i) and "
                        + "q(i) is at most (1 minus 1/m) times w. The center is common to the whole "
                        + "set K; convexity of K is not required.")),
                    Paragraph(Text(
                        "Write l(i) and u(i) for the attained coordinate extrema and put r equal to "
                        + "(1 minus 1/m) times w. The proposed coordinate intervals have lower "
                        + "endpoints max(0,u(i) minus r) and upper endpoints l(i) plus r. For every "
                        + "nonempty coordinate set S, choose j in S and a single source attaining "
                        + "u(j). Its other coordinates bound the corresponding upper extrema with "
                        + "an added w. Nonnegativity and total mass one give sum over S of u(i) at "
                        + "most 1 plus (cardinality of S minus 1) times w. Taking S to consist of "
                        + "coordinates with u(i) greater than r proves that the lower endpoints "
                        + "sum to at most one. A source attaining one lower extremum proves that "
                        + "the upper endpoints sum to at least one. Interpolating the endpoint "
                        + "vectors supplies mass one inside all intervals, hence the common center.")),
                    Paragraph(Text(
                        "This is a simplex specialization of the relative Jung bound in Amir, "
                        + "Proposition 2.12: the convex hull of K lies in an affine space of "
                        + "dimension m minus one. The argument uses the maximum coordinate norm "
                        + "and does not assert a nonexpansive normalization of arbitrary real vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simplex-deletion-minimax"),
                DeclarationHandle.Create(Prefix + "simplex_deletion_minimax"),
                H("Sharp deterministic risk at every noise scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(RelativeCenters),
                Blocks(
                    Paragraph(Text(
                        "For every integer m at least two and every real epsilon at least zero, "
                        + "the unknown source p is any probability vector on m coordinates. Its "
                        + "exact observation is the pair (1, i mapped to 1 minus p(i)). The input "
                        + "space is a real number times the space of m real coordinates, with "
                        + "the product maximum norm. Add any noise vector eta of norm at most "
                        + "epsilon, including noise in the first, empty-operation reading. Total "
                        + "mass one is known independently of that reading. An estimator is any "
                        + "function on the entire input space returning a probability vector; "
                        + "no linearity, continuity or measurability is required. Its worstCaseCost "
                        + "is the supremum of the maximum coordinate error over all actual source "
                        + "and admissible noise pairs. The infimum of these costs over all "
                        + "estimators equals the extended nonnegative real embedding of "
                        + "(1 minus 1/m) times min(2 times epsilon,1).")),
                    Paragraph(Text(
                        "For any possible observed datum, the consistent sources form a compact "
                        + "subset of the simplex of diameter at most min(2 times epsilon,1). "
                        + "Choose a common center for this set, and use a fixed simplex vertex "
                        + "when the set is empty. This defines an estimator on all inputs and "
                        + "proves the upper bound. The first reading imposes no additional source "
                        + "restriction when its noise is admissible.")),
                    Paragraph(Text(
                        "For the matching lower bound put w equal to min(2 times epsilon,1) and "
                        + "b equal to (1 minus w)/m. All m probability sources b plus w times a "
                        + "coordinate vertex admit the same full observation (1,1 minus b minus "
                        + "w/2 in each deletion coordinate). For any probability output, some "
                        + "coordinate is at most 1/m. Choosing the corresponding source forces "
                        + "error at least (1 minus 1/m) times w. This covers zero noise, small "
                        + "noise and saturation in one construction. The noise need not preserve "
                        + "the exact observation image. The theorem concerns deterministic "
                        + "estimators and does not formalize an effective center algorithm, "
                        + "randomized expected risk or unrestricted real-vector outputs."))),
                DescribeRole.Theorem))));
}
