using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FixedTreeCommonExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Separation/FixedTreeCommonExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One total extension describes the complete resource region of a fixed finite tree.",
        H("Common Extensions on Finite Trees"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-tree-shape"), DeclarationHandle.Create(Prefix + "Tree"),
                H("Finite trees and their coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A tree is a vertex-labelled coordinate leaf or a vertex-labelled node with "
                    + "a family of children indexed by Fin n, for an arbitrary natural n. "
                    + "Unary nodes retain their own identities. The leaves function recursively "
                    + "takes the union of the actual child coordinate sets. Full requires full "
                    + "children with pairwise disjoint coordinate sets. Original vertices may "
                    + "be assigned distinct labels. The root leaf "
                    + "set is the entire finite coordinate index. The zero-child single node "
                    + "represents the empty-input convention."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-tree-protocol"), DeclarationHandle.Create(Prefix + "Implementation"),
                H("Native local protocols"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each actual subtree has its own arbitrary message type. A leaf encoder "
                    + "reads only its coordinate. An internal table reads the complete tuple "
                    + "of its child messages. Evaluation recursively applies those tables. "
                    + "Message types and the output type may be infinite. Reachable counts "
                    + "only the image of execution on the nonempty promise D, and includes "
                    + "the original root message. Nodes indexes all actual original subtrees. "
                    + "Only the tables at those subtrees affect evaluation on the fixed tree; "
                    + "unused syntactic trees can be assigned unit message types and constant tables."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-tree-canonical"), DeclarationHandle.Create(Prefix + "canonical"),
                H("The response protocol"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a total task H, a node message is an element of the existing labelled "
                    + "response range at its descendant-leaf cut. This is the quotient by equality "
                    + "of responses on all complementary assignments. The local merger chooses "
                    + "a representative of the complete child-response profile and returns its "
                    + "parent response. On an unrealizable tuple it still returns a parent "
                    + "response. Finite sibling replacement proves that the parent response "
                    + "depends only on that child profile. Native execution therefore returns "
                    + "exactly the response of the actual subtree assignment."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-tree-common-extension"), DeclarationHandle.Create(Prefix + "result"),
                H("Common extension and attained minima"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite nonempty coordinate alphabets, an arbitrary finite labelled full "
                    + "tree and a nonempty promise D with task f:D to O, every correct native "
                    + "protocol has one total extension H of f whose capacity vector is bounded "
                    + "coordinatewise by its actual D-reachable vector. Retraction of each local "
                    + "result onto that node's promised image preserves execution on D. Locality "
                    + "and tree context replacement prove every cut bound for this same H.")),
                    Paragraph(Text(
                    "Conversely, the canonical protocol for every total extension H is correct "
                    + "on D. Its actual image at every node equals the image of that node's "
                    + "response on D, and its reachable count is at most the full response capacity. "
                    + "The two full vector families consequently have the same upward closure.")),
                    Paragraph(Text(
                    "Every coordinatewise monotone cost into any linearly ordered type has "
                    + "equal attained minima on the protocol and extension families. Each capacity "
                    + "is bounded by the number of full assignments, so the set of capacity vectors "
                    + "is finite even when O is infinite. A minimum on this finite set and the two "
                    + "native domination constructions give actual optimizing witnesses. Taking "
                    + "the maximum over all original nodes gives the peak minimum. Every "
                    + "zero-child constant node has exactly one D-reachable message; thus the "
                    + "single-node empty-input case has capacity one and both protocol and "
                    + "capacity peaks equal to one."))), DescribeRole.Theorem))));
}
