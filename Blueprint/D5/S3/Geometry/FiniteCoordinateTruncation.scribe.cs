using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteCoordinateTruncationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCoordinateTruncation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-coordinate support, truncation and homotopies in actual independence realizations.",
        H("Finite coordinate truncation"),
        Blocks(
            Node("probability", "Probability", "Probability coordinates",
                "For every finite vertex type V, Probability(x) means that all real coordinates x(a) are nonnegative and their sum over V is one.", DescribeRole.Definition),
            Node("avoid", "Avoid", "Independent coordinate support",
                "For every simple graph G and real coordinate vector x, Avoid(G,x) says that each G-edge has an endpoint with coordinate zero.", DescribeRole.Definition),
            Node("support", "support", "The nonzero support",
                "The finite support of a coordinate vector consists of precisely its nonzero coordinates.", DescribeRole.Definition),
            Node("support-nonempty", "support_nonempty", "Nonempty probability support",
                "Every nonnegative vector whose finite coordinate sum is one has nonempty support.", DescribeRole.Theorem),
            Node("independent-support-iff", "independent_support_iff", "Support independence",
                "For every finite simple graph G and vector x, its nonzero support is independent exactly when every edge has a zero endpoint. No probability assumption is needed.", DescribeRole.Theorem),
            Node("realization-iff", "realization_iff", "Actual independence realization",
                "For every finite simple graph G and vector x, membership in the existing coordinate realization of its actual independence complex is equivalent to Probability(x) and Avoid(G,x). The forward direction uses a face containing x; the reverse direction uses the finite nonzero support of x.", DescribeRole.Theorem),
            Node("ispace", "Ispace", "The native topological space",
                "Ispace(G) is the subtype of finite real coordinate space consisting of the actual realization of the nonempty independent faces of G. Its topology is the inherited subspace topology.", DescribeRole.Definition),
            Node("vertex", "vertex", "A coordinate vertex",
                "For each vertex a of G, the vector with coordinate one at a and zero elsewhere belongs to Ispace(G).", DescribeRole.Definition),
            Node("mix", "mix", "Straight coordinate interpolation",
                "For real t and vectors x,y, mix(t,x,y)(a)=(1-t)x(a)+ty(a). At t=0 and t=1 it is x and y respectively.", DescribeRole.Definition),
            Node("probability-mix", "probability_mix", "Probability along a segment",
                "For every pair of probability coordinate vectors and every t in the closed unit interval, their straight interpolation is again a probability vector.", DescribeRole.Theorem),
            Node("avoid-mix-of-support", "avoid_mix_of_support", "A segment with shrinking support",
                "If x avoids the edges of G and every zero coordinate of x is also zero in y, then every real straight interpolation of x and y avoids the edges of G.", DescribeRole.Theorem),
            Node("avoid-mix", "avoid_mix", "Compatible segments",
                "Suppose that for each G-edge at least one endpoint is zero in both x and y. Every real straight interpolation of x and y then avoids that edge.", DescribeRole.Theorem),
            Node("normalize", "normalize", "Coordinate normalization",
                "Normalize a vector by dividing every coordinate by its finite coordinate sum.", DescribeRole.Definition),
            Node("probability-normalize", "probability_normalize", "Positive normalization",
                "A nonnegative coordinate vector with strictly positive sum normalizes to a probability vector. A zero coordinate remains zero.", DescribeRole.Theorem),
            Node("cut", "cut", "Coordinate cutoff",
                "For a real threshold e, cut(e,x)(a)=max(x(a)-e,0). For e nonnegative it preserves every zero coordinate; it kills every coordinate at most e.", DescribeRole.Definition),
            Node("cut-sum-bound", "cut_sum_bound", "Total mass after cutoff",
                "For every probability vector x and every real e, the sum of cut(e,x) is at least 1-card(V)e. This estimate controls the strict normalization denominators in the star-gadget neighborhoods.", DescribeRole.Theorem),
            Node("continuous-normalize", "continuous_normalize", "Continuity of normalization",
                "For every topological parameter space, a continuous family of finite coordinate vectors has continuous normalization when its coordinate sum never vanishes.", DescribeRole.Theorem),
            Node("continuous-cut", "continuous_cut", "Continuity of variable cutoff",
                "A continuous finite-coordinate family and a continuous real threshold give a continuous cutoff family. This uses coordinatewise maxima of continuous real functions.", DescribeRole.Theorem),
            Node("continuous-mix", "continuous_mix", "Joint continuity of interpolation",
                "For every topological parameter space and two continuous finite-coordinate families, straight interpolation is jointly continuous on the unit interval times that space.", DescribeRole.Theorem),
            Node("straight", "straight", "A straight homotopy in a subspace",
                "Given continuous maps f,g into a specified coordinate subspace D and proofs that every straight interpolation remains in D, straight constructs their actual continuous homotopy. Membership, rather than a homotopy or retraction property, is its hypothesis.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
