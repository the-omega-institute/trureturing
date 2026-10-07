using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CapacityPortParityAbsorptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CapacityPortParityAbsorption.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every routing of a finite loopless capacity multigraph has literal terminal paths, exact typed terminal counts, and the parity absorption bound D ≥ 3q + 4b + 2c + o.",
        H("Capacity ports and parity absorption"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("literal-ports"),
                DeclarationHandle.Create(Prefix + "Port"),
                H("Real and slack ports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V and E be arbitrary finite types, each with decidable equality. An edge identity e has source src(e) and destination dst(e). Its two real ports are (e,false) and (e,true), with bases src(e) and dst(e). The incidence degree of v is the number of such real ports based at v. For r:V→Nat, add a distinct slack port (v,i) for every i<2r(v)−degree(v), using natural subtraction. Port is the disjoint sum of these two carriers; parallel edges retain distinct identities and ports. A leaf has capacity zero and incidence degree one. Its real port is an L terminal; every slack port is an H terminal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("literal-port-graph"),
                DeclarationHandle.Create(Prefix + "portGraph"),
                H("The two swaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The involution rho exchanges the two real ports of each actual edge and fixes slack ports. A routing sigma is an involution that preserves each port base and fixes exactly the L ports. The simple port graph joins distinct ports p,t when t=rho(p) or t=sigma(p). The real-edge swap changes base because the original graph is loopless; the local swap preserves base, so these two nonfixed neighbors are distinct."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("component-actual-length"),
                DeclarationHandle.Create(Prefix + "componentLength"),
                H("Count original edge identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected component kappa of the literal port graph, componentL and componentH count its L and H ports. Its actual length lambda is the number of identities e:E whose false real port belongs to that component. Define a as the number of components with two L ports, b as the number with two H ports, c as the number with one L and one H port, and o as the number with two L ports and odd lambda. These are counts of actual connected components, not assumed path data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("capacity-port-parity-absorption"),
                DeclarationHandle.Create(Prefix + "actual_capacity_port_parity_absorption"),
                H("Full routing theorem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all finite V,E, endpoint maps src,dst, natural capacities r, natural K0 and routing sigma, assume src(e)≠dst(e) for every e; r(v)=0 implies degree(v)≤1; r(v)>0 implies degree(v)≤2r(v); no edge has two zero-capacity leaves as endpoints; sigma is involutive, preserves bases and fixes exactly the L ports; and the number ell of leaf vertices is at most K0. Let C=|E|, R=sum_v r(v), q=C−R and D=R+K0, with q and D interpreted in Int.")),
                    Paragraph(Text("Every component containing a terminal has distinct terminal ports p,t and a simple port-graph path w from p to t. A port belongs to the component if and only if it belongs to the support of w. Every graph edge with both endpoints in that component occurs in w, including all local sigma edges. The only terminals in the component are p,t. For each original edge identity e, membership of its false port in the component is equivalent to the unordered pair of its two real ports occurring in w. The number of edges of w that are such real-port pairs equals lambda exactly.")),
                    Paragraph(Text("The typed counts obey ell=2a+c and sum_v(2r(v)−degree(v))=2b+c. The signed deficit obeys q=a−b, and D≥3q+4b+2c+o. LL components contain at least two actual edge identities, using the prohibition on an edge between two leaves; odd LL components contain at least three. LH components contain at least one. Counts of actual edges in distinct components are disjoint and sum to C.")),
                    Paragraph(Text("For every Bool coloring chi:V→Bool with chi(src(e))≠chi(dst(e)) for all original edges, and for every LL component and any two distinct L ports p,t in it, lambda is odd if and only if chi(base(p))≠chi(base(t)). Each real rho step flips the color and each sigma step preserves it; only real edges are counted. The inequality has no coloring hypothesis.")),
                    Paragraph(Text("Choose a maximum simple path rooted at a terminal by Nat.findGreatest. Its starting neighbor set is saturated because the root has one neighbor, and its internal neighbor sets are saturated because they have two neighbors and the ambient graph has at most two. A neighbor outside the endpoint support would extend the path. Every visited endpoint neighbor is already a path neighbor by saturation at the root or an internal vertex. Thus the path subgraph is closed under all ambient neighbors and equals the actual connected component. Injectivity of e↦{(e,false),(e,true)} supplies the exact real-edge count.")),
                    Paragraph(Text("Empty carriers and isolated zero-capacity vertices are included. Distinct HH terminal ports may have the same base, and an HH path may have actual length zero. Terminal-free components contribute their nonnegative actual lengths without any asserted cycle classification. This theorem does not assert the global LL-to-HH injection, q≤0, a concrete grid residual construction, or the unrestricted coefficient-one grid bound."))),
                DescribeRole.Theorem)),
        []));
}
