using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFPacketOwnershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFPacketOwnership.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be any finite vertex type and H any finite family of its subsets. Write N_H(p) for the vertices x outside p with insert(x,p) in H, and K_H(q) for the two-element ground sets p with q contained in N_H(p). An exact marked exchange determines the packet and row of either endpoint. No uniformity, disjoint-union uniqueness, or codegree cap is required for this local assertion.",
        H("Ownership at a marked exchange"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("packet-row"),
                DeclarationHandle.Create(Prefix + "PacketRow"),
                H("Actual packet-row membership"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("PacketRow(H,q,T,i,e) means that q has two elements, T has three elements, K_H(q) is exactly the family of all two-element subsets of T, i belongs to q, and e=insert(i,p) for some two-element subset p of T.")),
                    Paragraph(Text("The definition does not assume that q and T are disjoint. This follows from the common-link equality: every vertex of T belongs to an edge of its triangle, and each element of q must lie outside every such edge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("marked-endpoint-ownership"),
                DeclarationHandle.Create(Prefix + "marked_endpoint_ownership"),
                H("A marked endpoint determines its packet and row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let u,v,a,b,c be pairwise distinct vertices. Assume the two exact equalities N_H({u,b})={a,c} and K_H({a,c})={{u,b},{v,b}}. For every q,T,e and i, if e is either {u,a,b} or {u,b,c} and PacketRow(H,q,T,i,e), then q={u,v}, T={a,b,c}, i=u, and the intersection of q with e is the singleton {i}.")),
                    Paragraph(Text("For e={u,a,b}, write q={i,x} and T as its membership edge together with a third vertex y. The actual links force x and y outside e. The row element i is one of u,a,b. If i=a, the neighborhood equality forces x=c; the packet would then give three edges in K_H({a,c}), contradicting its exact two-edge value. If i=b, the triple {b,u,y} forces y=c. The packet then places {u,x} in K_H({a,c}); neither of its two allowed edges is possible. Thus i=u. The triple {u,b,y} again forces y=c, fixing T. The two extensions {x,a,b} and {x,b,c} place {b,x} in K_H({a,c}), forcing x=v and fixing q. Interchanging a and c proves the other endpoint case.")),
                    Paragraph(Text("This is conditional uniqueness: the theorem does not assume or assert the existence of a packet without a membership witness. When the designated packet is given, its marked endpoints therefore cannot belong to a second packet row. The singleton intersection also identifies the row element without a choice of representation."))),
                DescribeRole.Theorem)),
        []));
}
