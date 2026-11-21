using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class ConvexHullDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/ConvexHull.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consecutive normalized face counts are nonincreasing. The converse hull inclusion uses their consecutive differences as weights of full skeletons.",
        H("The real convex hull of proper f-vectors"),
        Blocks(
            Node("lym", "lym", "Consecutive local LYM inequality for proper downsets", DescribeRole.Theorem,
                "Apply the local LYM bound to the lower shadow of the next layer and use downward closure to bound this shadow by the current layer."),
            Node("skel", "skel", "Real skeleton vertices", DescribeRole.Definition,
                "Fill the layer capacity up to the cutoff and put zero above it, in real coordinates."),
            Node("skelset", "skelSet", "Positive skeleton vertices", DescribeRole.Definition,
                "Use the skeletons with cutoffs from one through n."),
            Node("lymchain", "lymChain", "Consecutive normalized inequalities", DescribeRole.Definition,
                "Require the fixed first two coordinates, nonnegativity and the comparison of adjacent ratios to the binomial capacities."),
            Node("fin-one-eq", "fin_one_eq", "Identify the singleton coordinate", DescribeRole.Theorem,
                "The degree-one index used in the inequalities is the same index as the singleton coordinate for positive ground size."),
            Node("convex-lymchain", "convex_lymChain", "The normalized region is convex", DescribeRole.Theorem,
                "The defining equalities and inequalities are linear. They hold under convex combinations."),
            Node("muof", "muOf", "Weights from consecutive ratio differences", DescribeRole.Definition,
                "Subtract the next normalized coordinate from the current one and use zero beyond the last degree."),
            Node("muof-of-le", "muOf_of_le", "The weight inside the coordinate window", DescribeRole.Theorem,
                "Inside the window the weight is the indicated normalized difference, with the next value zero at the boundary."),
            Node("muof-of-gt", "muOf_of_gt", "The weight beyond the coordinate window", DescribeRole.Theorem,
                "There are no coordinates past the last degree and the weight there vanishes."),
            Node("sum-mu-telescope", "sum_mu_telescope", "The weights telescope", DescribeRole.Theorem,
                "Summing the consecutive differences from a degree through the end recovers the normalized count in that degree."),
            Node("lymchain-subset-hull", "lymChain_subset_hull", "Normalized inequalities give a skeleton mixture", DescribeRole.Theorem,
                "The consecutive differences are nonnegative and sum to one. Their skeleton combination has the same coordinates by telescoping."),
            Node("rvector", "RVector", "Real f-vector coordinates", DescribeRole.Definition,
                "Use one real coordinate for each face size from zero through n."),
            Node("realvector", "realVector", "Realize an f-vector over the reals", DescribeRole.Definition,
                "Cast each natural coordinate to the reals."),
            Node("realvectors", "realVectors", "Real realizations of proper f-vectors", DescribeRole.Definition,
                "Take the image of the literal proper vector set under coordinatewise real casting."),
            Node("hull-eq-lymchain", "hull_eq_lymChain", "The literal convex hull is the normalized region", DescribeRole.Theorem,
                "Actual face vectors satisfy local LYM. Conversely the skeleton mixture expresses every point of the region using actual proper face vectors."),
            Node("cap-pos-real", "cap_pos_real", "Positive real layer capacities", DescribeRole.Theorem,
                "Cast the positive natural binomial capacity to the reals."),
            Node("normalized", "Normalized", "The normalized coordinates at a scale", DescribeRole.Definition,
                "Fix the first two coordinates at their scaled capacities. Require nonnegative coordinates and monotone normalized counts."),
            Node("ratio-le", "ratio_le", "Compare any two normalized coordinates in order", DescribeRole.Theorem,
                "Apply the antitonicity field at the two indices."),
            Node("lymchain-iff-normalized", "lymChain_iff_normalized", "Adjacent and all-index comparisons at scale one", DescribeRole.Theorem,
                "Consecutive comparisons imply antitonicity on the finite chain. The reverse implication restricts to adjacent indices."),
            Node("mem-dilate-iff", "mem_dilate_iff", "Test membership in the actual real dilate", DescribeRole.Theorem,
                "Use the hull equality and cancel the positive dilation factor in the coordinate and ratio conditions."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-convex-hull-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name is "lym" or "lymChain_subset_hull" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
