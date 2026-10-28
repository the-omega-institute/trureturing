using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class DirectLeechDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/DirectLeechDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct real selfduality from integer Golay congruences", H("Direct real selfduality from integer Golay congruences"),
        Blocks(
            Node("claim-1", "eight_mem", "Coordinate probes belong to the literal construction",
                "Eight times each coordinate vector satisfies the parity, binary code and modulo-eight sum conditions. These vectors both constrain real dual coordinates and prove that the actual lattice spans the full real coordinate space.", DescribeRole.Theorem),
            Node("claim-2", "raw_integer_construction_dual_eq", "Direct selfduality without determinant or covolume assumptions",
                "For any binary selfdual doubly even code, the real integer image of its literal parity, quotient-code and modulo-eight sum conditions is selfdual under dot divided by eight, provided its pairing is integral. The proof constructs every probe from those conditions. Eight times a coordinate vector forces dual coordinates integral. Four times coordinate differences forces common parity. Twice each binary codeword lift forces code membership by binary selfduality. The vector one minus four times the zeroth coordinate vector recovers the complete sum condition. The proved integral pairing gives the converse inclusion directly.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
