using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent edge networks joined at one vertex admit an exact transformation of their complete terminal partition law.",
        H("Independent substitution at a single gate"),
        Blocks(
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
                + "require no separate limiting argument.")), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-product-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
