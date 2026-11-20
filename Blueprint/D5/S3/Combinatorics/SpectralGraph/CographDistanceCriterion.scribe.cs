using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CographDistanceCriterionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Cographs/mannamandaltura2026spectralcographs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cotree criteria for multiplicity equality.",
        H("Exact cotree criteria for multiplicity equality"),
        Blocks(
            Entry("Eligible", "Eligible shift",
                "The real shift differs from both −1 and −2.", DescribeRole.Definition),
            Entry("kernelCount", "Local nullity",
                "Take the real dimension of the kernel of the local operator.", DescribeRole.Definition),
            Entry("distanceMultiplicity", "Distance multiplicity",
                "Take the real nullity of the ordinary distance matrix shifted by x. Real symmetry identifies geometric and algebraic multiplicity.", DescribeRole.Definition),
            Entry("cotree_kernelCount_le_and_saturation", "Local width bound and saturation",
                "At eligible shifts and with nonzero internal coupling, nullity is bounded by vicinal width. Saturation forces a kernel vector whose coordinates sum to a nonzero value."),
            Entry("distanceMultiplicity_le", "Distance multiplicity bound",
                "At every eligible shift the nullity of a connected cograph is at most its width."),
            Entry("JoinRootCriterion", "Join-root criterion",
                "There is a unique nonleaf child and a positive number of root leaves. The leaves are the universal vertices. The child has nullity one below its width and scalar response g with 1+g−ℓ/(x+1)=0.", DescribeRole.Definition),
            Entry("distanceMultiplicity_eq_width_iff_joinRoot", "Equality at width above one",
                "At a fixed eligible real shift equality is equivalent to the join-root criterion."),
            Entry("distanceMultiplicity_eq_width_iff_singleton", "Singleton equality",
                "A singleton attains exactly at zero."),
            Entry("distanceMultiplicity_eq_width_iff_width_one", "Equality at width one",
                "At an eligible shift, equality at width one holds exactly when there is a nonzero distance eigenvector."),
            Entry("width_one_attains", "Attainment at width one",
                "The singleton uses zero. For a nonsingleton the native distance matrix is nonzero and symmetric with zero trace, so it has a positive eigenvalue."),
            Entry("cotreeScalarState", "Cotree scalar state",
                "At a common real shift record the nullity and either nonzero pairing on the kernel or the scalar response.", DescribeRole.Definition),
            Entry("cotreeScalarState_spec", "Correctness of the scalar recursion",
                "The three rank-one transitions compute the native state at every real shift under the stated label condition, including poles and coincident roots."),
            Entry("CotreeGuardData", "Guard data",
                "Store the response numerator, a monic guard and the set of distinct descendant guards.", DescribeRole.Definition),
            Entry("cotreeGuardData", "Guard recursion",
                "The leaf guard is X+q. At a node use the product of child guards plus the coupling times the common response numerator.", DescribeRole.Definition),
            Entry("cotreeGuardData_degrees", "Degrees of uncancelled guards",
                "Each guard is monic of subtree-size degree. The numerator has degree one lower and leading coefficient minus the subtree size."),
            Entry("cotreeGuardData_off_roots", "States away from roots",
                "Outside all descendant guard roots the native nullity vanishes and the scalar response is the uncancelled rational ratio."),
            Entry("distanceMultiplicity_guard_candidates", "Exact finite set of shifts",
                "At each real x, eligible equality is equivalent to membership in the distinct guard-root set, eligibility and equality of the recursive nullity with the width. The sum of the distinct guard degrees bounds the cardinality."),
            Entry("distanceMultiplicity_attains_iff", "Classification of attaining cographs",
                "Width-one connected cographs attain. At greater width, attainment is equivalent to the join-root criterion holding at an eligible real guard root."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("cographdistancecriterion-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
