using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class CoherentFlagPortDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite classical flags do not lower the necessary coherent dimension below a preserved probe component; explicit complement-filled decoders are trace preserving on entire port blocks.",
        H("CoherentFlagPort"),
        Blocks(
            Paragraph(Text("A finite port consists of actual rectangular encoder and decoder Kraus families. The encoder is normalized jointly over flags; the decoder is normalized separately for every flag on the entire coherent block. Flag probabilities may depend on the input. The actual encoder and decoder also have canonical completely positive trace-preserving realizations on the ambient flagged matrix algebra; their Kraus matrices encode only classical diagonal sectors and discard cross-sector coherences during decoding. Every composite Kraus matrix factors through the same port index space, so its rank is at most that coherent dimension. Probability preservation gives scalar action on each component. Normalization guarantees a nonzero scalar on each component, forcing its dimension below the port dimension. For a partial isometry J with adjoint Gram projection P, the decoder maps Y to J adjoint times Y times J plus the trace of the unused port complement times a fixed density. This acts on all matrices in the port block. The fixed density is a sum of rank-one factors of total squared norm one; choosing these factors inside the component makes it supported there. Bluhm, Rauber, and Wolf Sections 4 and 7.1 supply the classical-quantum compression model and the maximal-block construction.")),
            Describe.Lean(
                DescribeId.Create("flagged-cptp-roundtrip"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CoherentFlagPort.flagged_cptp_roundtrip"),
                H("flagged cptp roundtrip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("Every normalized rectangular finite flagged port admits canonical completely positive trace-preserving encoder and decoder maps. The encoder image is proved to have zero entries between distinct classical flag sectors for every matrix input. Their all-matrix composition is exactly the same-flag Kraus composite used by the coherent dimension lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("port-component-lower-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CoherentFlagPort.port_component_lower_bound"),
                H("port component lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("Any normalized finite flagged port preserving all probe probabilities on every density input has coherent dimension at least the complex dimension of each probe component span."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("padded-decoder-cptp"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_cptp"),
                H("padded decoder cptp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("For a partial-isometry Gram projection and a normalized finite fixed-state factorization, the explicit decoder Kraus family is normalized and supplies a canonical completely positive trace-preserving channel. Its all-matrix action includes the fixed-state complement filler."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("padded-decoder-corner"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_corner"),
                H("padded decoder corner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("The same whole-block decoder maps every encoded component corner to P times the original matrix times P, with vanishing filler contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("component-pinching-port"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CoherentFlagPort.component_pinching_port"),
                H("component pinching port"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression"), LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary")),
                Blocks(Paragraph(Text("A complete finite family of component projections, partial-isometry embeddings into one coherent block, and normalized fixed-state factors determines an actual finite flagged port whose composite equals the component pinching map on every matrix."))),
                DescribeRole.Theorem))));
}
