using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCactusSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangle with one pendant terminal realizes determinant ratios arbitrarily close "
            + "to two with strictly interior independent edge rates.",
        H("A sharp cactus family for three-terminal bond percolation"),
        Blocks(
            Node("IsCactus", "Cactus graphs", DescribeRole.Definition,
                "For every decidable vertex type V and simple graph G, IsCactus G means "
                    + "that every two simple cycles with different undirected edge sets "
                    + "have at most one common vertex. Rotations and reversals of one "
                    + "cycle have the same edge set and are identified."),
            Node("pendantEnds", "The four-edge source graph", DescribeRole.Definition,
                "The vertices are a=0,b=1,c=2,d=3 and the indexed edges are db,bc,dc,ad, "
                    + "in that order. Their independent opening rates are u,v,s,A."),
            Node("pendant_law", "The complete actual source law", DescribeRole.Theorem,
                "For all real u,v,s,A, let p=law pendantEnds 0 1 2 [u,v,s,A]. Its five "
                    + "masses in the order separate,ab,bc,all,ac are "
                    + "((1-A)(1-v)(1-us)+A(1-u)(1-v)(1-s), Au(1-v)(1-s), "
                    + "(1-A)(v+us-vus)+Av(1-u)(1-s), A(uv+us+vs-2uvs), As(1-u)(1-v)). "
                    + "The actual reachability partition is evaluated on all sixteen "
                    + "open-edge configurations before the product weights are summed."),
            Node("pendant_determinant", "The retained triangle contribution", DescribeRole.Theorem,
                "For all real rates u,v,s,A, put K=uv+us+vs-2uvs and "
                    + "L=(1-s)(u+v-uv). For the actual four-edge law p, "
                    + "delta(p)=p(ac)[L+(1-A)K]."),
            Node("pendant_bound", "The complete four-edge rate family", DescribeRole.Theorem,
                "For all u,v,s,A in [0,1], the actual four-edge law p satisfies "
                    + "0 <= delta(p) <= 2p(ac). Both K and L are nonnegative, "
                    + "and L+(1-A)K=u+v-suv-AK <= 2. This covers all boundary "
                    + "rates as well as every interior member of the sharp family."),
            Node("pendant_sharp_formula", "Exact sharp-family numerator", DescribeRole.Theorem,
                "For every real t and p=law pendantEnds 0 1 2 [1-t,1-t,t,t], "
                    + "Z=p(ac)=t^4 and delta(p)=t^4(2-4t+4t^2-4t^3+2t^4). "
                    + "This equality uses no division and includes t=0."),
            Node("pendant_cactus", "Cycle structure", DescribeRole.Theorem,
                "The full graph with all four edges present is a cactus. Its pendant "
                    + "edge ad is a bridge, hence belongs to no simple cycle. Every "
                    + "simple cycle has at least three distinct edges, so its edge set "
                    + "is exactly the triangle db,bc,dc. There are no two distinct "
                    + "simple cycles under the edge-set convention."),
            Node("pendant_sharpness", "Strict interior sharpness at two", DescribeRole.Theorem,
                "For every real epsilon>0 there are independent edge rates theta:Fin 4 -> R "
                    + "such that the full four-vertex graph is connected and a cactus, "
                    + "every rate lies strictly between zero and one, Z=law(theta,ac)>0, "
                    + "and delta(law(theta))>(2-epsilon)Z. Set t=min(epsilon/8,1/4) "
                    + "and theta=[1-t,1-t,t,t]. The exact numerator above is greater "
                    + "than (2-4t)Z, which exceeds (2-epsilon)Z."),
            Paragraph(Text(
                "The sharp family rules out every uniform cactus constant below two. "
                    + "A uniform upper bound for all cactus graphs additionally requires "
                    + "a full five-partition-preserving central-cycle and independent-arm "
                    + "reduction. That graph reduction is not supplied by this module."))),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-cactus-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
