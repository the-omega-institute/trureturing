using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ActualRectangularSaturatedGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ActualRectangularSaturatedGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasibility on an actual even rectangle produces blank vertices across saturated tiles and separates adjacent saturated occupied points.",
        H("Saturated geometry of an even rectangle"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-even-rectangular-saturated-geometry"),
            DeclarationHandle.Create(Prefix + "actual_even_rectangular_saturated_geometry"),
            H("The actual geometry conjunction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every positive natural a,b, finite type E with decidable equality, maps src,dst:E→Fin(2a)×Fin(2b), and finite set T of rectangle vertices, assume every src(e),dst(e) pair is square-grid adjacent, the endpoint map E×Bool→Fin(2a)×Fin(2b) is injective, and both endpoints of each edge lie outside T. The endpoint map sends (e,false) to src(e) and (e,true) to dst(e). Put A=(T union image(src)) union image(dst), where both images range over all E. Assume that for every x in T the set of vertices y in A square-grid adjacent to x has cardinality at most one. Square-grid adjacency means one coordinate agrees and the other differs by one, using the integer embeddings of the natural coordinates.")),
                Paragraph(Text("The tile map kappa sends x to (floor(x.row/2),floor(x.column/2)) in Fin a×Fin b. For each tile Q, let t(Q) count T in its kappa fibre; h(Q) count edge identities whose two endpoints have tile Q; and s(Q) count identities with exactly one endpoint in Q and the other endpoint in a distinct tile containing exactly two T vertices. Set r(Q)=2−(t(Q)+h(Q)+s(Q)), with natural subtraction. ER consists of actual edge identities whose endpoint tiles differ and both contain fewer than two T vertices. Set rs(e)=kappa(src(e)), rd(e)=kappa(dst(e)), and chi(Q)=decide(Odd(Q.row+Q.column)). For i,j in Fin 2, corner(Q,(i,j))=(2Q.row+i,2Q.column+j), and flip(i)=1−i in Fin 2.")),
                Paragraph(Text("The conclusion is the conjunction of the following twenty clauses, with all their displayed variables universally quantified unless an existence quantifier is stated.")),
                Paragraph(Text("1. T is a subset of A. 2. For each e in E, src(e) and dst(e) belong to A. 3. For each x in T and all y,z in A, adjacency of both y and z to x implies y=z.")),
                Paragraph(Text("4. For each Q and i in Fin 2×Fin 2, kappa(corner(Q,i))=Q. 5. For each Q the map corner(Q,−) is injective. 6. For each Q,x, kappa(x)=Q if and only if there exists i in Fin 2×Fin 2 with corner(Q,i)=x. 7. For each Q,i,j, the two corners are adjacent if and only if (i.row=j.row and i.column≠j.column) or (i.column=j.column and i.row≠j.row).")),
                Paragraph(Text("8. For each e in ER, rs(e)≠rd(e), their tiles are square-grid adjacent, and chi(rs(e))≠chi(rd(e)). 9. For each Q, t(Q)≤2. 10. For each Q, t(Q) is the sum of the four indicators that corner(Q,(0,0)), corner(Q,(0,1)), corner(Q,(1,0)), and corner(Q,(1,1)) belong to T, each indicator being one when membership holds and zero otherwise.")),
                Paragraph(Text("11. For each Q and i,j,k in Fin 2×Fin 2, if j≠k, both j and k satisfy the corner-adjacency condition with i, corner(Q,i) belongs to T, and corner(Q,j),corner(Q,k) belong to A, then False. 12. For each i in Fin 2, flip(i)≠i. 13. For each i,j in Fin 2×Fin 2, if j satisfies the corner-adjacency condition with i, then j=(flip(i.row),i.column) or j=(i.row,flip(i.column)).")),
                Paragraph(Text("14. For each distinct Q,Q' and i,j in Fin 2×Fin 2, suppose corner(Q,i) and corner(Q',j) are adjacent, t(Q)=2, and corner(Q,i) belongs to A but not T. There exist actual rectangle vertices z,w such that z belongs to T, kappa(z)=Q, kappa(w)=Q', corner(Q,i) is adjacent to z, corner(Q',j) is adjacent to w, z is adjacent to w, and w does not belong to A.")),
                Paragraph(Text("15. For all actual rectangle vertices x,y in different tiles, if x,y are adjacent, t(kappa(x))=t(kappa(y))=2, and both x and y belong to A but not T, then False. This concerns all actual adjacent vertices, including pairs not selected as matching edges. 16. For each e in E whose endpoint tiles differ, those tiles cannot both have t=2.")),
                Paragraph(Text("17. For each Q with t(Q)=2, h(Q)=0. 18. For each such Q, s(Q)=0. 19. For each such Q, degree(rs,rd,Q)=0, where degree counts actual ER endpoint incidences, including distinct parallel-edge identities. 20. For any actual adjacent x,y in different tiles, if t(kappa(x))=2 and x belongs to A but not T, there exists an actual vertex w with kappa(w)=kappa(y), w adjacent to y, and w outside A.")),
                Paragraph(Text("A saturated tile with an occupied non-T corner has its two adjacent corners in T and its opposite corner outside A. Flipping the coordinate transverse to an intertile edge constructs the z,w in clause 14. Feasibility at z forces w outside A. Clause 15 follows because saturation at y would force this same w into T.")),
                Paragraph(Text("These actual blank vertices restrict attachments, and saturated separation closes the zero-capacity edge contradiction in "), Ref("D5/S3/Combinatorics/Graph/ActualRectangularResidualBridge.actual_even_rectangular_residual_bridge"), Text(". The result is a general structural theorem for every realization satisfying the original feasibility conditions; it enumerates no fixed positive instance."))),
            DescribeRole.Theorem)),
        []));
}
