using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class GolayEncoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/GolayEncoder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/leech1967packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit extended Golay code",
        H("Explicit extended Golay code"),
        Blocks(
            Node("claim-1", "encode", "Carryless polynomial encoding",
                "The actual linear map from twelve binary message coordinates to twenty-four coordinates multiplies by g, with no wraparound, and appends its parity coordinate.", DescribeRole.Definition),
            Node("claim-2", "reference_encoder_identification", "The reciprocal convention is identified exactly",
                "The reference polynomial from Elkies is related by explicit reversal of the message and first twenty-three coordinate positions, fixing parity.", DescribeRole.Theorem),
            Node("claim-3", "parity_extension", "The last coordinate is the parity bit",
                "The twenty-fourth coordinate equals the binary sum of the first twenty-three coordinates for every message.", DescribeRole.Theorem),
            Node("claim-4", "encode_injective", "The encoder loses no messages",
                "A finite matrix inverse certificate proves a left inverse, hence injectivity of the actual encoder.", DescribeRole.Theorem),
            Node("claim-5", "code_finrank", "Dimension twelve",
                "The linear image has dimension twelve by injectivity and upstream linear algebra.", DescribeRole.Theorem),
            Node("claim-6", "code_card", "All 4096 messages remain distinct",
                "The actual linear image has exactly 4096 words.", DescribeRole.Theorem),
            Node("claim-7", "weight_spectrum", "Kernel-checked weights of all actual words",
                "Sixty-four small kernel certificates cover all 4096 messages. The only weights are zero, eight, twelve, sixteen and twenty-four. This is a spectrum assertion, not an exact enumerator count.", DescribeRole.Theorem),
            Node("claim-8", "doubly_even", "Double evenness",
                "Every word in the actual linear image has Hamming weight divisible by four.", DescribeRole.Theorem),
            Node("claim-9", "minimum_weight", "Nonzero words have weight at least eight",
                "The computed spectrum together with the weight-zero characterization yields the universal lower bound.", DescribeRole.Theorem),
            Node("claim-10", "all_ones_mem", "The all-ones carry word belongs",
                "The encoder applied to message 3189 is the actual all-ones word needed for odd plus odd integer-vector closure.", DescribeRole.Theorem),
            Node("claim-11a", "octad_mem", "The encoded octad belongs to the linear image",
                "Its message witness is retained by the actual encoder-image definition and is consumed by the shortest-vector construction.", DescribeRole.Theorem),
            Node("claim-11", "octad_weight", "An encoded weight-eight word",
                "The octad is the encoder applied to message one, not a separately supplied codeword.", DescribeRole.Theorem),
            Node("claim-12", "self_orthogonal", "Orthogonality from the generator",
                "The actual generator has zero Gram matrix, yielding orthogonality of every pair of its linear-image words.", DescribeRole.Theorem),
            Node("claim-13", "self_dual", "Self-duality",
                "A small kernel-checked matrix splitting identity reconstructs every orthogonal vector through the actual encoder, giving equality with the orthogonal complement.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
