using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TriangleEJMGramInterfaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exact bridge for PR #15164 has been formalized over rational weights. The regular tetrahedron Gram entries produce the three EJM probability classes 25/256, 1/256 and 5/256, and the three independent source visibilities produce an explicit eight-term multi-affine mixture. These declarations are probability identities only. They do not assert triangle locality of EJM and do not provide an inflation certificate.",
        H("Exact EJM Gram probabilities and independent-source noise"),
        Blocks(
            Node("gram", "Regular tetrahedron Gram entry",
                "tetrahedralGram",
                "The exact rational inner product is 1 for equal tetrahedral vertices and -1/3 for distinct vertices.",
                DescribeRole.Definition),
            Node("probability", "EJM Gram probability",
                "ejmGramProbability",
                "P(a,b,c) is defined as (4 + S + 6R)/256, where S is the pairwise Gram sum and R is the symmetric quadratic cycle term in the three pairwise Gram entries.",
                DescribeRole.Definition),
            Node("table", "Exact EJM probability table",
                "ejmGramProbability_table",
                "Kernel-checked by finite case analysis. All equal outputs have probability 25/256, exactly two equal outputs have probability 1/256, and all distinct outputs have probability 5/256. The accompanying mass theorem proves that the 64 entries sum to one and nonnegativity is proved separately.",
                DescribeRole.Theorem),
            Node("law", "Finite probability carrier",
                "ejmFiniteLaw",
                "The EJM table is packaged as Erdos7.FiniteLaw over the three-party output type. This reuses the repository finite rational probability structure.",
                DescribeRole.Definition),
            Node("weight", "Independent-source noise weights",
                "sourceNoiseWeight",
                "The eight weights correspond to the eight choices of ideal or maximally mixed state on the alpha, beta and gamma source edges.",
                DescribeRole.Definition),
            Node("noise", "Independent-source noise map",
                "independentSourceNoise",
                "The noisy table is the exact weighted sum of eight component tables. The theorem independentSourceNoise_eight_terms expands this definition into the eight-term multi-affine polynomial from the theory supplement.",
                DescribeRole.Definition),
            Node("mass", "Noise coefficient normalization",
                "sourceNoiseWeight_mass",
                "The eight source weights sum to one for arbitrary rational visibilities. This is the normalization identity for the source-typed mixture.",
                DescribeRole.Theorem),
            Node("affine", "Edge-wise affinity",
                "independentSourceNoise_affine_alpha",
                "The source-specific map is affine in each edge visibility. This is a polynomial identity and is not a locality or nonlocality result.",
                DescribeRole.Theorem)
        ),
        []private);

    private static DocumentBlock Node(
        string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("triangle-ejm-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);
}
