using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFLocalPacketsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFLocalPackets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be any finite vertex type and H a finite disjoint-union-free family of subsets of V. Fix a member e of cardinality three. The actual local graph records replacements of one coordinate of e by a vertex outside e. Its mixed vertices correspond precisely to triangle packets containing e in the designated row. The other members of H need not have cardinality three.",
        H("Mixed vertices and actual triangle packets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-packet-correspondence"),
                DeclarationHandle.Create(Prefix + "mixed_packet_correspondence"),
                H("Exact local-to-packet correspondence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write N_H(p) for the vertices x outside p such that insert(x,p) belongs to H, and K_H(q) for the two-element sets p with q contained in N_H(p). Let w=(u,v) belong to localVertices(H,e): u is in e, v is outside e, and insert(v,e without u) belongs to H. Two local vertices are adjacent when their replaced coordinates and their external labels are distinct and the triple formed by both external labels and the remaining coordinate belongs to H.")),
                    Paragraph(Text("There are two actual neighbors of w with different replaced coordinates if and only if there exists a unique three-element set T for which PacketRow(H,{u,v},T,u,e) holds. This means that K_H({u,v}) is exactly the family of two-element subsets of T and e=insert(u,p) for some two-element subset p of T. The row pair has two elements. No codegree bound or additional packet assumption is needed.")),
                    Paragraph(Text("For the forward implication, choose mixed neighbors (a,c) and (b,d). Their distinct coordinates give e={u,a,b}. Actual replacement and adjacency triples place {b,c} and {a,d} in K_H({u,v}), together with {a,b}. The common link is intersecting. Since c and d lie outside e, intersection of the first two edges forces c=d. The local correspondence gives exactly three edges in the common link. Its three displayed edges therefore exhaust the two-element subsets of T={a,b,c}. The base edge places e in row u.")),
                    Paragraph(Text("Conversely, write the row edge as p={a,b} and its three-element triangle as T={a,b,c}, with c outside p. Every common-link edge extends by either u or v to an actual member of H and excludes both row vertices. Thus c lies outside e, and the packet triples give actual local vertices (a,c) and (b,c), each adjacent to w. Their replaced coordinates differ, proving mixedness.")),
                    Paragraph(Text("Uniqueness follows because a three-element set is the union of all its two-element subsets. Equal triangle edge families therefore have equal vertex sets. This correspondence reconstructs the local packet; it does not assert a global allocation or counting bound."))),
                DescribeRole.Theorem)),
        []));
}
