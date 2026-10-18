using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalBondDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalBond.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent edge opening on the four-vertex star gives an exact five-partition law. "
            + "Its base determinant lies between zero and the exceptional partition mass, "
            + "and constants below one fail with strictly interior edge rates.",
        H("Three-terminal independent bond laws on a star"),
        Blocks(
            Paragraph(Text(
                "The terminal labels are a=0, b=1 and c=2. Vertex 3 is the center. "
                    + "Mode.separate means a|b|c; Mode.ab means ab|c; Mode.bc means a|bc; "
                    + "Mode.all means abc; Mode.ac means ac|b. The five coordinates in that "
                    + "order correspond to null, low, high, both endpoints and middle. "
                    + "Here Z is the mass of Mode.ac, not the mass of Mode.all.")),
            Node("Mode", "The five actual partitions", DescribeRole.Definition,
                "Mode is the finite type with constructors separate, ab, bc, all and ac. "
                    + "These stand for a|b|c, ab|c, a|bc, abc and ac|b respectively."),
            Node("openGraph", "Open graph", DescribeRole.Definition,
                "For endpoint data ends:E -> V x V and a configuration omega:E -> Bool, "
                    + "two distinct vertices are adjacent when an open indexed edge has "
                    + "those endpoints in either order. This defines a simple undirected graph."),
            Node("connected", "Actual path observation", DescribeRole.Definition,
                "For finite V and E with decidable equality on V, connected ends omega x y "
                    + "is the Boolean decision of the existence of a walk from x to y "
                    + "in openGraph ends omega."),
            Node("partition", "Three-terminal partition", DescribeRole.Definition,
                "For finite V and E, endpoints ends, terminals a,b,c and configuration omega, "
                    + "partition first tests a connected to b, then b connected to c, "
                    + "then a connected to c. The resulting label records their actual "
                    + "connectivity partition. Transitivity rules out inconsistent pair readings."),
            Node("weight", "Independent configuration mass", DescribeRole.Definition,
                "For a finite edge type E, rates theta:E -> R and configuration omega, "
                    + "weight theta omega is the product over e of theta(e) if e is open "
                    + "and 1-theta(e) if e is closed. Rates in [0,1] give nonnegative masses "
                    + "whose sum over the complete Boolean configuration cube is one."),
            Node("weight_sum", "Normalization of the independent source", DescribeRole.Theorem,
                "For every finite decidable edge type E and every theta:E -> R, "
                    + "the sum of weight theta omega over all omega:E -> Bool is one. "
                    + "Expand the product of theta(e)+(1-theta(e)) over all edges. "
                    + "Nonnegativity additionally requires theta(e) in [0,1]."),
            Node("sum_cube_succ", "A first-coordinate split", DescribeRole.Theorem,
                "For every natural n and every real function f on Fin(n+1) -> Bool, "
                    + "the sum of f over that configuration cube equals the sum over "
                    + "x:Bool and omega:Fin(n)->Bool of f(Fin.cons x omega). "
                    + "The bijection splits the first edge state from the remaining edges."),
            Node("law", "Connectivity pushforward", DescribeRole.Definition,
                "For finite decidable vertex and edge types, endpoints ends, terminals a,b,c, "
                    + "rates theta and mode s, law ends a b c theta s is the sum of "
                    + "weight theta omega over precisely those configurations whose "
                    + "actual partition is s. No connectivity probability is stipulated."),
            Node("delta", "Base determinant", DescribeRole.Definition,
                "For every p:Mode -> R, delta(p)=p(separate)*p(all)-p(ab)*p(bc)."),
            Node("starEnds", "Three independent star edges", DescribeRole.Definition,
                "For e in Fin 3, starEnds(e)=(3,e). The resulting full graph is the "
                    + "star with center 3 and leaves 0,1,2."),
            Node("star_law", "All five star probabilities", DescribeRole.Theorem,
                "For all real A,B,C, let p=law starEnds 0 1 2 [A,B,C]. Then, in the "
                    + "mode order separate, ab, bc, all, ac, p is exactly "
                    + "(1-AB-AC-BC+2ABC, AB(1-C), (1-A)BC, ABC, A(1-B)C). "
                    + "The identity holds even outside the probability interval as a polynomial "
                    + "identity for the finite configuration sums. Within [0,1] these are "
                    + "the independent bond probabilities."),
            Node("star_determinant", "Determinant factorization", DescribeRole.Theorem,
                "For all real A,B,C and the actual star law p, "
                    + "delta(p)=B(1-AC)*p(ac). The formula has no division and includes Z=0."),
            Node("star_bound", "Uniform constant one on the star", DescribeRole.Theorem,
                "For every A,B,C in the closed interval [0,1], the actual star law p "
                    + "satisfies 0 <= delta(p) <= p(ac). Indeed p(ac) is nonnegative "
                    + "and 0 <= B(1-AC) <= 1."),
            Node("star_sharpness", "Strict interior sharpness", DescribeRole.Theorem,
                "For every real epsilon>0 there are rates theta:Fin 3 -> R such that "
                    + "the full graph is a tree, every theta(e) lies strictly between zero "
                    + "and one, all five law masses are nonnegative and sum to one, "
                    + "Z=law(theta,ac)>0, and delta(law(theta))>(1-epsilon)Z. "
                    + "Set t=min(epsilon/4,1/4), A=C=t and B=1-t. Then Z=t^3 and "
                    + "delta/Z=(1-t)(1-t^2)>1-epsilon."),
            Paragraph(Text(
                "ThreeTerminalTree.tree_law preserves the complete five-partition law of "
                    + "every finite-edge tree through three disjoint path edge sets; "
                    + "ThreeTerminalTree.tree_bound therefore extends the constant-one bound "
                    + "to all such trees. Cactus graphs and bounded block cycle rank still "
                    + "require their respective graph reductions."))),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-bond-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
