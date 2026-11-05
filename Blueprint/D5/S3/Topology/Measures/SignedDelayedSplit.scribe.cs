using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedDelayedSplitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedDelayedSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Delayed whole-fibre signed splitting",
        H("Delayed whole-fibre signed splitting"),
        Blocks(
            Describe.Lean(DescribeId.Create("delayed-fibre-pools"),
                DeclarationHandle.Create(Owner + "exists_delayed_fibre_pools"),
                H("Two original source reservoirs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A continuous onto map from a compact first-countable space, a separating family of Boolean coordinates and eventual whole-support fibre constancy are given. Each original intersection J with N(e) is infinite and J is contained in I. Points y(n) lie in their original supports and in a fixed clopen Q. The conclusion chooses points f(n) over y(n), infinite subsets S(e) of those exact intersections and points z(e) over Q. Along S(e), f converges to z(e), and every clopen neighborhood of z(e) eventually contains the entire fibre over y(n). Old fibres need not be singletons."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("delayed-pool-plan"),
                DeclarationHandle.Create(Owner + "exists_delayed_pool_plan"),
                H("Internal equal and distinct cluster alternatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two original reservoirs are disjoint. Pool selection gives two cluster points internally. If they are equal, the original parity pools give the two target column pools with a common whole-fibre limit. If they differ, a clopen separates the points and, after finite thinning, separates all target fibres in the two source sets. One of these source pools is split into two infinite subsets: one remains the source reservoir and the other supplies an independent target reserve. Both target column parities use that reserve. The remaining source pool retains the other original parity. This distinguishes column parity from source reservoir parity without assuming a common cluster point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-ordered-split"),
                DeclarationHandle.Create(Owner + "exists_parity_ordered_split"),
                H("Literal ordered refinement and signed estimates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The core takes two infinite target pools whose whole fibres tend to one specified point, and signed reference data for the auxiliary rows. A finite history fixes its earlier exclusion first. The next target index is chosen from the column's prescribed pool so that its entire target fibre avoids that exclusion. The new clopen H is literally the inverse image of V(n) intersect Q minus the exclusion. Its finite tests are fixed next; auxiliary indices are selected only afterward. Their supports avoid the cluster point, and every norm-preserving signed lift satisfies the uniform finite signed marginal estimate.")),
                    Paragraph(Text("The increasing columns give one closed Boolean split and an onto old projection. The true sheet lies over Q. Whole-support fibre constancy holds on selected target and auxiliary supports. Every target fibre lies on the sheet prescribed by column parity. The finite strict bounds thirteen forty-eighths and one sixth are retained. Auxiliary references are common to all lift selections along each increasing fixed-label column subsequence; actual norm-preserving lifts supply inhabited reference classes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internal-delayed-split"),
                DeclarationHandle.Create(Owner + "exists_internal_delayed_split"),
                H("One split with internally selected pools and source reference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This theorem consumes the pool alternative and the literal ordered core. It selects its target reference internally, covers both equal and distinct cluster points, and returns two infinite source sets inside the original J and N(e). In the distinct case every source index avoids the target reserve, so the new coordinate is false on its entire original support. In the equal case the selected column parities give the source sets. A clopen of the same split separates the entire fibres over the prescribed y(n).")),
                    Paragraph(Text("All target slices lie above Q. For source signed measures carried by a disjoint clopen P, the true sheet is absent over P. Old signed F transfers to a genuine successor reference on the selected source union. Eventual whole-support constancy then gives the same regular signed limit for every lift selection: the existential reference precedes the universal selection. No singleton old fibre, desired target reference or vacuous all-lifts branch is assumed.")),
                    Paragraph(Text("SignedDelayedSuccessor uses this same split to define the final row sets, replace the source subsequence and initialize residual signed references. The construction concerns compact metric local successors; it does not assert an ordinal history or a final omega-one construction."))),
                DescribeRole.Theorem))));
}
