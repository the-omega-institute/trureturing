using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class CanonicalFlagCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical CPTP maps with classical flag outputs have the same component-dimension bound as normalized finite Kraus ports.",
        H("CanonicalFlagCompression"),
        Blocks(
            Paragraph(Text("The encoder and decoder use the existing canonical all-amplification completely positive trace-preserving channel interface. Classical output means that distinct flag sectors have zero matrix entries for every matrix input; it imposes no input independence on flag probabilities. Their canonical finite Kraus representations restrict to encoder rows and decoder columns in each flag sector. Trace preservation normalizes the encoder jointly and the decoder separately on each entire coherent block. The encoded matrices are block diagonal, so their actual decoder action is exactly the same-flag rectangular Kraus composite. The probability-preserving component lower bound therefore applies directly to arbitrary canonical channels in the classical-quantum compression model of Bluhm, Rauber, and Wolf.")),
            Describe.Lean(
                DescribeId.Create("canonical-flag-port-factorization"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_factorization"),
                H("canonical flag port factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression")),
                Blocks(Paragraph(Text("Any canonical CPTP encoder with classical flag output and canonical CPTP decoder admit a normalized finite Kraus port with identical all-matrix composite action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-flag-port-lower-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_lower_bound"),
                H("canonical flag port lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("For arbitrary unit probe families and arbitrary finite classical flags, canonical CPTP encoding and decoding that preserve every probe probability for every density input have coherent block dimension at least every actual component dimension."))),
                DescribeRole.Theorem))));
}
