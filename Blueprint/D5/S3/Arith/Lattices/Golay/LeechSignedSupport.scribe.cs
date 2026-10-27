using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class LeechSignedSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/LeechSignedSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/nebe2014leechcatalogue");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed supports and parity reconstruction",
        H("Signed supports and parity reconstruction"),
        Blocks(
            Paragraph(Text("Binary signs on a finite support give literal integer coordinates. Their sum, square sum and binary reduction retain the sign parity and the support. Deleting one coordinate gives a two-sided parametrization of even sign assignments. These elementary coordinate identities assert no lattice classification.")),
            Node("leechsignedsupport-signed", "signed", "Literal signed coordinates",
                "For every integer k, finite support S among twenty-four positions, and binary sign function on S, signed k S assigns k times the corresponding sign on S and zero elsewhere. Signs are indexed by S itself, without an ordering.", DescribeRole.Definition, false),
            Node("leechsignedsupport-signed-squaresum", "signed_squareSum", "Square sum of a signed support",
                "For every integer k, support S and sign assignment on S, squareSum of signed k S is k squared times the cardinality of S. Zero scale and empty support are included.", DescribeRole.Theorem, false),
            Node("leechsignedsupport-signed-injective", "signed_injective", "Signs at a nonzero scale are recoverable",
                "For each nonzero integer k and support S, the map sending signs on S to signed k S is injective. Coordinate cancellation recovers every sign.", DescribeRole.Theorem, false),
            Node("leechsignedsupport-exists-signed", "exists_signed", "Reconstruction from coordinate values",
                "For any integer k, support S and integer vector x, if x is zero off S and equals k or minus k on S, some binary sign assignment on S reconstructs x exactly. The case k equal to zero is included.", DescribeRole.Theorem, false),
            Node("leechsignedsupport-signed-two-red", "signed_two_red", "Binary reduction recovers the support word",
                "For every binary word c and every sign assignment on its nonzero support, dividing signed 2 (wordSupport c) coordinatewise by two and reducing modulo two recovers c, for both positive and negative signs.", DescribeRole.Theorem, false),
            Node("leechsignedsupport-evensignsequiv", "evenSignsEquiv", "One parity coordinate is determined",
                "For every support S and chosen element p of S, even binary sign assignments on S are equivalent to arbitrary assignments on the elements distinct from p. The missing bit is the sum of the others, so the total binary sum is zero.", DescribeRole.Definition, false),
            Node("leechsignedsupport-evensigns-card", "evenSigns_card", "An octad has 128 even sign assignments",
                "Every support of cardinality eight has exactly 128 even sign assignments. Deleting one coordinate leaves seven independent binary choices.", DescribeRole.Theorem, false),
            Node("leechsignedsupport-evensigns-of-sum-div-two", "evenSigns_of_sum_div_two", "Integer divisibility implies binary parity",
                "For any support S and binary sign assignment, if the sum of lifted bits is divisible by two, the binary sum is zero. Together with the converse this converts the coordinate-sum congruence into the octad sign restriction.", DescribeRole.Theorem, false))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role, bool attested) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(),
            attested ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
