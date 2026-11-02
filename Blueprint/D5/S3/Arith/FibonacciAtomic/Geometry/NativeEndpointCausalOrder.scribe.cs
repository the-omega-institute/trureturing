using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeEndpointCausalOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact local and creating-split edges generate the native endpoint order.",
        H("Native endpoint causal order"), Blocks(
        Paragraph(Text("The finite event set and original Call labels are NativeEndpointEventIdeals.events. First chooses the root promotion for alpha birth or root split for beta birth, requiring actual membership. Edge recursively contains exactly a local promotion-before-split edge when both occur, a parent split edge to the first existing local event of either child, and the corresponding shifted edges inside each child. There is no edge into an inactive alpha terminal, and a beta terminal born beta has no event.")),
        Describe.Lean(DescribeId.Create("native-endpoint-causal-order"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder.result"),
            H("Exact transitive-closure correspondence"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every birth type, every target and every two members of its endpoint-labelled finite event set, the transitive closure of Edge relates their original Calls exactly when the induced prefix/phase order strictly relates them. This also covers empty and singleton event sets. The result identifies the order used by native execution adequacy with the exact causal order defined in Atomic Generation Acquisition AA17.2; it is consumed for every promised comb by NativePromiseCausalBoundary.result.")),
            Paragraph(Text("Every generating edge strictly increases the prefix/phase order. Conversely, structural induction finds the first local event before any event in a nonempty child. A parent split reaches that first event directly and then follows the child induction. A root promotion first reaches the root split. Events in one child lift that child's generating path; distinct children cannot be related by prefix ancestry. Thus every strict comparison has an actual path of the specified local edges. Antisymmetry of the existing partial order excludes directed cycles.")),
            Paragraph(Text("The correspondence proves source-specific causal structure, with no execution, reachability, rational clock, chosen serial order or probability-law premise. Full seven/eight laws remain outside this module."))), DescribeRole.Theorem))));
}
