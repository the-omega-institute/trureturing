using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.TauCeti.AlgebraicTopology.Singular;

internal sealed class OrderedCechDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered Cech-singular double complex.", H("The ordered Cech-singular double complex"), Blocks(
            Node("bicomplex", "bicomplex", "Ordered intersections in each simplicial degree",
                "For a simplicial set A covered by a linearly ordered family P of subcomplexes, the ordered intersection complexes in each simplicial degree form rows. Alternating singular face maps define a commuting bicomplex with coefficients in an object R of an abelian category with the required coproducts.", DescribeRole.Definition),
            Node("horizontalaugmentation", "horizontalAugmentation", "The specified augmentation",
                "In each singular degree the horizontal augmentation is the ordered-cover augmentation on the same simplex generators. It sends each singleton-indexed simplex to that simplex and is zero in positive ordered degree.", DescribeRole.Definition),
            Node("horizontal-total-comparison", "horizontal_total_comparison", "The finite-degree total comparison",
                "In an abelian category with the required coproducts, if P covers in every simplicial degree, the actual horizontal total map induces homology isomorphisms in degrees zero and one and an epimorphism in degree two. The ordered-cover chain contraction and finite-degree bicomplex comparison apply to this specified map.", DescribeRole.Theorem),
            Node("isiso-coefficientaugmentation-of-contractible", "isIso_coefficientAugmentation_of_contractible", "Contractible singular columns",
                "For any coefficient object R in an abelian category with the required coproducts, any contractible topological space X, and every natural degree q, its actual singular coefficient-sum augmentation induces a degree-q homology isomorphism. In degree zero this is the singular H0 augmentation. Positive degrees use reduced singular homology and contractibility; the target complex is concentrated at zero.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
