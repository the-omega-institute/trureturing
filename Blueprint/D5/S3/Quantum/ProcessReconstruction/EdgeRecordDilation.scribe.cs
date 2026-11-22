using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordDilationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordDilation";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tracing out the finite input, edge and site records gives the edge record channel on every matrix.",
        H("Environment Record Isometry and Partial Trace"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-isometry"),
                DeclarationHandle.Create(Module + ".dilation_isometry"),
                H("The coherent finite record map is an isometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "A computational input x maps to an equal-amplitude sum over all edge words e "
                    + "and site words r. Each summand has system label localOutput(b,x,e,r) and "
                    + "environment label (x,e,r). Orthogonal input labels give orthogonal "
                    + "columns, and the squared amplitudes sum to one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-environment-trace"),
                DeclarationHandle.Create(Module + ".trace_environment_eq_channel"),
                H("Tracing the record register gives the channel action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Lean verifies the equality for every complex input matrix X. In the "
                    + "partial trace of V X V†, each environment sum pairs the same label "
                    + "(x,e,r) on the bra and ket. This leaves X(x,x) times the uniform record "
                    + "pushforward into the diagonal output entries."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a joint qubit and environment matrix, the same entrywise partial trace "
                + "is used in EnvironmentRecords.traceEnvironment.")),
            Paragraph(Text(
                "The accompanying paper proof realizes this record isometry on an open "
                + "nearest-neighbor path using ten layers, including an optional final endpoint "
                + "CNOT, and at most six ancillas per site including the output qubit. All "
                + "ancillas start in the product of zero states. Each site has an output, a "
                + "fair site register and its garbage copy, an outgoing edge register and its "
                + "garbage copy where an edge leaves the site, and an incoming edge copy "
                + "where an edge enters the site.")),
            Paragraph(Text(
                "In layers 1 and 2, apply local Hadamards to the site and outgoing edge "
                + "registers and copy each into its garbage register. Layers 3 and 4 copy "
                + "outgoing edge bits across even and odd edges, respectively. Layers 5 "
                + "and 6 use Toffolis controlled by the input and the incoming or outgoing "
                + "edge bit to update the output. Layer 7 flips the inputs. Layer 8 applies "
                + "the Toffoli controlled by the flipped input and the site bit. Layer 9 "
                + "restores the inputs, and layer 10 applies the endpoint CNOT when b = 1. "
                + "The two intersite layers each use vertex-disjoint edges.")),
            Paragraph(Text(
                "For each basis input, the circuit gives the stated output and one "
                + "equal-amplitude term per record. The copied and garbage registers are "
                + "determined by (x,e,r). Their inclusion in the discarded system preserves "
                + "orthogonality of the record labels and leaves the same partial trace. "
                + "The layer schedule, ancilla count and circuit semantics are established "
                + "by the paper proof.")))));
}
