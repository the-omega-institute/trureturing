using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class GolayOctadIncidenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/GolayOctadIncidence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/nebe2014leechcatalogue");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Golay Steiner system and coordinate incidence",
        H("The Golay Steiner system and coordinate incidence"),
        Blocks(
            Paragraph(Text("The octads are the weight-eight words of the original polynomial Golay encoder image. Their supports form the classical Steiner system S(5,8,24). The attribution follows Conway and Sloane through the extended Golay code reference in the library note; no novelty is claimed. Minimum distance and finite double counting prove the statements without assuming a design or a transitive symmetry group.")),
            Node("golayoctadincidence-steiner-five", "steiner_five", "Unique octad through five coordinates",
                "For every five-element subset T of the twenty-four coordinates, there is exactly one octad whose word support contains T. Binary subtraction gives the symmetric difference of supports. Minimum nonzero weight eight forces distinct octads to meet in at most four coordinates. Thus forgetting the octad from an octad–five-subset flag is injective. The source and target cardinalities are 759 times binomial(8,5) and binomial(24,5), both 42504, so this projection is bijective."),
            Node("golayoctadincidence-coordinate-incidence", "coordinate_incidence", "Incidence at two arbitrary distinct coordinates",
                "For arbitrary distinct coordinates i and j, exactly 253 octads contain i and 253 contain j; exactly 77 contain both, 352 contain exactly one, and 330 contain neither. Counting five-subsets containing a prescribed singleton gives 35 times its octad incidence equal to 8855. Counting those containing a prescribed pair gives 20 times its incidence equal to 1540. The disjoint occupancy cases then give the remaining counts. These support incidences are inputs for signed Leech-vector distributions; they do not assert a completed axis-shell distribution."))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
