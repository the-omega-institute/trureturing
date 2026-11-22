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
                "Apply the local LYM bound to the lower shadow of the next layer and use downward closure to bound this shadow by the current layer. Snellman's Spine/LYM.lean, line 46, states the inequality for order ideals."),
            Node("skel", "skel", "Real skeleton vertices", DescribeRole.Definition,
                "Fill the layer capacity up to the cutoff and put zero above it, in real coordinates. See Spine/LYM.lean, line 76."),
            Node("skelset", "skelSet", "Positive skeleton vertices", DescribeRole.Definition,
                "Use the skeletons with cutoffs from one through n. See Spine/LYM.lean, line 80."),
            Node("lymchain", "lymChain", "Consecutive normalized inequalities", DescribeRole.Definition,
                "Fix the first two coordinates, compare adjacent ratios to the binomial capacities, and require a nonnegative last coordinate. See Spine/LYM.lean, line 85."),
            Node("fin-one-eq", "fin_one_eq", "Identify the singleton coordinate", DescribeRole.Theorem,
                "The degree-one index used in the inequalities is the same index as the singleton coordinate for positive ground size. See Spine/LYM.lean, line 94."),
            Node("convex-lymchain", "convex_lymChain", "The normalized region is convex", DescribeRole.Theorem,
                "The defining equalities and inequalities are linear. They hold under convex combinations. See Spine/LYM.lean, line 102."),
            Node("muof", "muOf", "Normalized coordinates extended by zero", DescribeRole.Definition,
                "At degree k through n, divide x[k] by the binomial coefficient choose(n,k). Extend the ratio by zero beyond n. See Spine/LYM.lean, line 164 and Part III, Proposition 2, equation (14)."),
            Node("muof-of-le", "muOf_of_le", "The ratio inside the coordinate window", DescribeRole.Theorem,
                "For k at most n, the value is x[k] divided by choose(n,k), including at k = n. See Spine/LYM.lean, line 167."),
            Node("muof-of-gt", "muOf_of_gt", "The ratio beyond the coordinate window", DescribeRole.Theorem,
                "For k greater than n, the extended ratio is zero. See Spine/LYM.lean, line 171."),
            Node("sum-mu-telescope", "sum_mu_telescope", "Consecutive ratio differences telescope", DescribeRole.Theorem,
                "Summing each ratio minus the next from degree k through n recovers the ratio at k, since the extended ratio at n+1 is zero. See Spine/LYM.lean, line 176."),
            Node("lymchain-subset-hull", "lymChain_subset_hull", "Normalized inequalities give a skeleton mixture", DescribeRole.Theorem,
                "The barycentric weight of the skeleton at cutoff k is the ratio at k minus the ratio at k+1. These weights are nonnegative and sum to one. Their skeleton combination has the same coordinates by telescoping. See Spine/LYM.lean, line 197 and Part III, Proposition 2 at scale one."),
            Node("rvector", "RVector", "Real f-vector coordinates", DescribeRole.Definition,
                "Use one real coordinate for each face size from zero through n."),
            Node("realvector", "realVector", "Realize an f-vector over the reals", DescribeRole.Definition,
                "Cast each natural coordinate to the reals, as in the image map in Counting/Duality.lean, line 322."),
            Node("realvectors", "realVectors", "Real realizations of proper f-vectors", DescribeRole.Definition,
                "Take the image of the literal proper vector set under coordinatewise real casting. Counting/Duality.lean, line 322, identifies this image with the real carrier in Spine/Complexes.lean, line 68."),
            Node("hull-eq-lymchain", "hull_eq_lymChain", "The literal convex hull is the normalized region", DescribeRole.Theorem,
                "Actual face vectors satisfy local LYM. Conversely the skeleton mixture expresses every point of the region using actual proper face vectors. See Spine/KozlovThm.lean, line 145."),
            Node("cap-pos-real", "cap_pos_real", "Positive real layer capacities", DescribeRole.Theorem,
                "Cast the positive natural binomial capacity to the reals."),
            Node("normalized", "Normalized", "The normalized coordinates at a scale", DescribeRole.Definition,
                "Fix the first two coordinates at their scaled capacities. Require nonnegative coordinates and monotone normalized counts."),
            Node("ratio-le", "ratio_le", "The scale bounds each normalized coordinate", DescribeRole.Theorem,
                "Compare each degree with degree zero by antitonicity. The degree-zero ratio equals the scale."),
            Node("lymchain-iff-normalized", "lymChain_iff_normalized", "Adjacent and all-index comparisons at scale one", DescribeRole.Theorem,
                "Consecutive comparisons imply antitonicity on the finite chain. The reverse implication restricts to adjacent indices."),
            Node("mem-dilate-iff", "mem_dilate_iff", "Test membership in the actual real dilate", DescribeRole.Theorem,
                "Use the hull equality and cancel the positive dilation factor in the coordinate and ratio conditions. This is the Kozlov specialization of Part III, Proposition 2."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-convex-hull-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name is "lym" or "skel" or "skelSet" or "lymChain" or "fin_one_eq" or "convex_lymChain"
                or "muOf" or "muOf_of_le" or "muOf_of_gt" or "sum_mu_telescope" or "lymChain_subset_hull"
                or "realVector" or "realVectors" or "hull_eq_lymChain" or "mem_dilate_iff"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
