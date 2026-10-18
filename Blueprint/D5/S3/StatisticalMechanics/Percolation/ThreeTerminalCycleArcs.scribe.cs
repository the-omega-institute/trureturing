using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCycleArcsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycleArcs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A simple finite cycle reduces, configuration by configuration, to the triangle "
            + "of its three all-open arc events. This preserves the full terminal partition.",
        H("Three-terminal cycle arc reduction"),
        Blocks(
            Node("next", "The cyclic successor", DescribeRole.Definition,
                "For every natural n and e in Fin(n+3), next(e) is e+1 when that vertex "
                    + "is below n+3, and is zero otherwise."),
            Node("cycleEnds", "Actual cycle edge coordinates", DescribeRole.Definition,
                "For every natural n, cycleEnds n indexes the ordinary cycle of n+3 vertices "
                    + "by the same Fin(n+3) edge type: coordinate e has endpoints (e,next(e)). "
                    + "The last coordinate is the wraparound edge."),
            Node("arcSupport", "Arc coordinate support", DescribeRole.Definition,
                "For all natural n,l,r, arcSupport n l r is the finite set of actual "
                    + "cycle edge coordinates e satisfying l <= e.val < r."),
            Node("arcBit", "All-open arc event", DescribeRole.Definition,
                "For every natural n, edge configuration omega:Fin(n+3)->Bool and natural "
                    + "l,r, arcBit omega l r is true exactly when every coordinate in "
                    + "arcSupport n l r is open."),
            Node("cycle_reachable_iff", "Two complementary arcs", DescribeRole.Theorem,
                "For every natural n, configuration omega and vertices l,r of Fin(n+3) "
                    + "with l.val < r.val, l reaches r in openGraph(cycleEnds n,omega) "
                    + "if and only if either every edge e with l.val <= e.val < r.val is open, "
                    + "or every edge e with e.val < l.val or r.val <= e.val is open. "
                    + "The reverse implication constructs the forward path or the path through "
                    + "the wraparound edge. For the forward implication, a closed edge in each "
                    + "arc determines an ordinal interval cut. Every open edge preserves membership "
                    + "in that cut while the two terminals lie on opposite sides."),
            Node("core_partition", "Triangle configuration readout", DescribeRole.Theorem,
                "For all Boolean bits p,q,r, the actual triangleArms partition with edge "
                    + "bits [p,q,r,true,true,true] is read by the three relations "
                    + "p or (q and r), q or (p and r), and r or (p and q), with the "
                    + "usual five-mode priority. The finite open-graph computation checks "
                    + "all eight triangle configurations with constant-open pendant edges."),
            Node("cycle_partition", "Complete five-mode preservation", DescribeRole.Theorem,
                "For every natural n, configuration omega and ordered gates 0 < i.val < j.val < n+3, "
                    + "the graphMode of (0,i,j) on the actual open cycle equals the partition "
                    + "on triangleArmsEnds with edge bits [arcBit omega 0 i.val, "
                    + "arcBit omega i.val j.val, arcBit omega j.val (n+3), true,true,true]. "
                    + "All three pair relations are preserved simultaneously: the first pair "
                    + "uses the first arc or the conjunction of the other two; the second pair "
                    + "uses the second arc or the conjunction of the other two; the remaining "
                    + "pair uses the third arc or the conjunction of the first two. "
                    + "No probabilistic marginal fitting or conditioning is used."),
            Node("arcSupport_partition", "Disjoint source coordinates", DescribeRole.Theorem,
                "For every natural n and gates i,j with i.val <= j.val, the supports "
                    + "arcSupport n 0 i.val, arcSupport n i.val j.val and arcSupport n j.val (n+3) "
                    + "are pairwise disjoint and their union is all cycle edge coordinates. "
                    + "Adjacent gates yield a one-edge support; the wraparound edge belongs "
                    + "to the third support."),
            Node("cycleVertex", "Coordinates of an actual simple cycle", DescribeRole.Definition,
                "For every graph G, vertex a, simple closed walk p:a->a and equality "
                    + "p.length=n+3, cycleVertex p hp hlen embeds Fin(n+3) into the ambient "
                    + "vertex type by e -> p.getVert e.val. Simplicity proves injectivity "
                    + "before the final repeated vertex."),
            Node("cycleEdgeEquiv", "Actual undirected edge coordinates", DescribeRole.Definition,
                "For every graph G, vertex a, simple closed walk p:a->a and equality "
                    + "p.length=n+3 and G.edgeSet=p.edgeSet, cycleEdgeEquiv is a bijection from Fin(n+3) to G.edgeSet. "
                    + "Coordinate e is the undirected edge joining p.getVert e.val to "
                    + "p.getVert(e.val+1). The simple-cycle trail property proves distinct "
                    + "coordinates have distinct actual undirected edges, and the walk's "
                    + "edge-list enumeration proves surjectivity."),
            Node("walk_cycle_partition", "Actual cycle network", DescribeRole.Theorem,
                "For every graph G, vertex a, walk p:a->a with hp:p.IsCycle, natural n, "
                    + "equality p.length=n+3, configuration omega and gates i,j with "
                    + "0 < i.val < j.val, form the network whose coordinate e joins "
                    + "p.getVert e.val and p.getVert(e.val+1). Its graphMode on "
                    + "(a,p.getVert i.val,p.getVert j.val) equals the same triangle partition "
                    + "of three all-open arc bits with constant-open pendant bits. "
                    + "An injective vertex relabelling and its inverse on the image preserve "
                    + "reachability; the last edge closes at p.getVert p.length=a. "
                    + "The network contains the cycle edges, not arbitrary additional edges "
                    + "of the ambient graph. All deterministic configurations are included."),
            Node("cycle_ordered_coordinates", "Arbitrary marked terminals", DescribeRole.Theorem,
                "For every graph G, simple closed walk p:v->v, and three pairwise distinct "
                    + "vertices a,b,c in p.support, there exist a simple closed walk q:a->a, "
                    + "natural n, equality q.length=n+3, equality q.edgeSet=p.edgeSet, "
                    + "and indices i,j in Fin(n+3) with 0 < i.val < j.val, "
                    + "q.getVert i.val=b and q.getVert j.val=c. Rotate p to a, then "
                    + "reverse it exactly when the indices of b and c occur in the opposite "
                    + "order. No ambient graph edge is changed by these operations."),
            Node("bond_cycle_partition", "Actual graph-edge source", DescribeRole.Theorem,
                "For every graph G, vertex a, simple closed walk p:a->a of length n+3, "
                    + "equality G.edgeSet=p.edgeSet, actual edge configuration omega:G.edgeSet->Bool, "
                    + "and ordered gates 0 < i.val < j.val, put xi(e)=omega(cycleEdgeEquiv p hp hlen hedges e). "
                    + "The graphMode of bondGraph G omega at (a,p.getVert i.val,p.getVert j.val) "
                    + "equals the triangleArms partition with bits [arcBit xi 0 i.val, "
                    + "arcBit xi i.val j.val, arcBit xi j.val (n+3),true,true,true]. "
                    + "The edge-set equality states that G itself is the cycle-edge graph, "
                    + "with optional additional isolated vertices. The source coordinates are "
                    + "the actual undirected edges of G, without duplicates.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-cycle-arcs-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
