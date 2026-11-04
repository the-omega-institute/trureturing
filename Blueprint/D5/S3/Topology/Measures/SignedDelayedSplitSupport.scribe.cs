using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedDelayedSplitSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedDelayedSplitSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed source limits and delayed columns",
        H("Signed source limits and delayed columns"),
        Blocks(
            Describe.Lean(DescribeId.Create("common-source-on-split"),
                DeclarationHandle.Create(Owner + "common_source_on_split"),
                H("A common source limit for every signed lift selection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The split is closed with an onto old projection. Its true sheet lies over Q, disjoint from the source clopen P. The source signed measures have total variation at most one, are carried by P and by their clopen supports, and satisfy old every-choice weak convergence along J. On an infinite subset M of J, both the old coordinates and the new Boolean coordinate are eventually constant on whole support fibres. A genuine norm-preserving lift supplies a reference. The conclusion selects one signed measure on this same split, with total variation at most one and regular positive and negative Jordan parts, to which every norm-preserving lift selection converges along M."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-delayed-column"),
                DeclarationHandle.Create(Owner + "exists_literal_delayed_column"),
                H("One literal delayed column after a finite ordered history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An infinite target pool has whole fibres converging to the specified point z. The target signed measures are the prescribed Dirac measures. Auxiliary rows retain their signed norm-preserving lifts, support nullity, reference convergence, disjoint supports and whole-support coordinate constancy. The construction fixes the earlier finite exclusion, chooses the next target index, and defines H literally as the inverse image of V(n) intersect Q minus that exclusion. It then fixes finite tests and chooses auxiliary indices. The resulting ordered column satisfies the original signed finite estimates, its entire target fibre lies in H, and all selected auxiliary supports avoid z. SignedDelayedSplit consumes this column in its parity construction and consumes the common source limit in its internal delayed split. These are constituent proofs of the compact metric local construction, with no ordinal-history or final-cube assertion."))),
                DescribeRole.Theorem))));
}
