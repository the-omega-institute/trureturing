using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent edge networks joined at one vertex admit an exact transformation of their complete terminal partition law.",
        H("Independent substitution at a single gate"),
        Blocks(
            Node("partition_graphMode", "The two readings of an actual graph partition", DescribeRole.Theorem,
                "For finite vertex and edge types, every endpoint map, three marked vertices "
                + "and every Boolean edge configuration, partition equals graphMode of the "
                + "same openGraph. This identifies Boolean reachability decisions with the "
                + "propositional reading used by the graph-theoretic source bridges."),
            Node("detachThird", "Detaching the third label", DescribeRole.Definition,
                "For a partition s of three labelled terminals and a Boolean connection bit, "
                + "detachThird keeps s when the bit is true. When false, all and ab become ab, "
                + "while separate, bc and ac become separate."),
            Node("reliability", "Actual two-terminal reliability", DescribeRole.Definition,
                "For finite vertex and edge types, an endpoint map f, vertices g,c and real "
                + "edge rates rho, reliability f g c rho is the finite Bernoulli product sum "
                + "over exactly the open subgraphs in which g reaches c. Rates in [0,1] give "
                + "a probability, including deterministic rates and g=c."),
            Node("joined_network_law", "The five probabilities under network substitution", DescribeRole.Theorem,
                "Let E and F be finite disjoint edge coordinate types on a common finite "
                + "vertex type V. The endpoint maps e and f are supported in vertex sets A "
                + "and B whose intersection is contained in the singleton {g}. Let a,b lie "
                + "in A and c in B, and give the two edge families arbitrary real rates theta "
                + "and rho. Put p=law e a b g theta and q=reliability f g c rho. The actual "
                + "law on the sum edge type E+F with endpoint map Sum.elim e f and independent "
                + "rates Sum.elim theta rho has masses all=q*p(all), ab=p(ab)+(1-q)*p(all), "
                + "bc=q*p(bc), ac=q*p(ac), and separate=p(separate)+(1-q)*(p(bc)+p(ac)). "
                + "The statement identifies the complete five-mode pushforward. It uses "
                + "the same independent configurations for every entry, without division "
                + "by a probability. Endpoints and terminals may coincide, and rates 0 or 1 "
                + "require no separate limiting argument."),
            Node("cycle_law_and_invariant", "Independent arc compression on any cycle length", DescribeRole.Theorem,
                "For every n in Nat, ordered indices 0<i<j<n+3, and edge rates theta in [0,1], "
                + "the actual independent bond law of the cycle with vertices Fin(n+3) and "
                + "successor edges, marked at 0,i,j, equals a triangle law with three unit arms "
                + "and three rates u,v,r in [0,1]. Each rate is the all-open probability of "
                + "one of the three disjoint arcs. The equality holds for all five partition "
                + "masses simultaneously. The law satisfies delta>=0 and the stronger bound "
                + "delta+p(all)*p(ac)<=2*p(ac). The finite product pushforward groups original "
                + "edge coordinates by their disjoint arc supports, including deterministic "
                + "rates and zero-mass boundary cases."),
            Node("gateTerminals", "The three main-network labels", DescribeRole.Definition,
                "For a port a,b or c, replace that labelled terminal by the gate g, leaving "
                + "the other two labels in their order."),
            Node("outerTerminal", "The attached label", DescribeRole.Definition,
                "For a port a,b or c and three vertices a,b,c, select the vertex at that port."),
            Node("Supported", "The side membership condition", DescribeRole.Definition,
                "The two labels other than the port lie in A, and the selected label lies in B."),
            Node("joined_network_transfer", "The complete source transformation at any port", DescribeRole.Theorem,
                "For the same finite independent edge families and single-gate support "
                + "hypotheses as joined_network_law, at any of the three ports, suppose "
                + "Supported holds. Then the actual five-mode source on the sum edge type "
                + "equals the product pushforward transfer of the main source with the "
                + "gate replacing that port, and the actual attached-network reliability "
                + "between the gate and the selected external terminal. Rates are arbitrary "
                + "real numbers in this exact finite-sum identity; labels may coincide."),
            Node("joined_network_ignored", "A terminal-free side is invisible", DescribeRole.Theorem,
                "For finite independent edge families supported at one gate, if a,b,c all "
                + "lie in A and the gate lies in B, the complete actual sum-network law is "
                + "exactly the law on the A network. This holds for arbitrary real rates."),
            Node("joined_network_invariant", "Actual graph substitution preserves the bound", DescribeRole.Theorem,
                "For the same single-gate networks, any port satisfying Supported, all "
                + "edge rates in [0,1], and any real C>=1, suppose the main law p with the "
                + "gate replacing that port satisfies delta(p)>=0 and "
                + "delta(p)+p(all)*p(ac)<=C*p(ac). Then both inequalities hold for the actual "
                + "sum-network source. The reliability is the finite actual connection "
                + "probability of the attached network. No division or strict positivity "
                + "is used."),
            Node("joined_network_signed_invariant", "Actual substitution preserves the absolute bound", DescribeRole.Theorem,
                "For the same single-gate networks, any port satisfying Supported, all "
                + "edge rates in [0,1], and real C>=1, suppose the main law p with the gate "
                + "replacing that port satisfies |delta(p)|+p(all)*p(ac)<=C*p(ac). Then the "
                + "same absolute strengthened bound holds for the actual sum-network source. "
                + "This consumes attachment_signed_invariant after the exact complete-law "
                + "substitution identity, using the attached network's actual finite-product "
                + "reliability. No sign assumption, division or strict positivity is used.")), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-product-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
