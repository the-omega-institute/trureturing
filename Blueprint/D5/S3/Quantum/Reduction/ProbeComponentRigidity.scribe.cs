using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class ProbeComponentRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal density-input probability preservation forces scalar Kraus action on the complex span of each nonorthogonality component.",
        H("ProbeComponentRigidity"),
        Blocks(
            Paragraph(Text("Let unit complex vectors form an arbitrary index family in a finite dimensional Hilbert space. Nonzero overlap generates an equivalence relation. Each class determines the span of all probes in that class. Probability preservation is required for every density input, rather than only an individual input state. The dual map fixes every probe projection. Expanding the positive sum of squared Kraus commutators forces each commutator to vanish. The scalar actions agree across nonzero overlaps, extend along finite chains, and then extend linearly over the whole component. Mayer and Knill Theorem 1 gives the connected rigidity statement; Koashi and Imoto give broader nondisturbance structure.")),
            Describe.Lean(
                DescribeId.Create("kraus-normalized-of-channel"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_normalized_of_channel"),
                H("kraus normalized of channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression")),
                Blocks(Paragraph(Text("Trace preservation of a canonical rectangular channel implies adjoint-Gram normalization for every finite Kraus representation. The channel scalarity and canonical flagged-port factorization consume this supplier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-preserving-kraus-commute"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.probability_preserving_kraus_commute"),
                H("probability preserving kraus commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For every normalized finite Kraus representation preserving each probe probability on all density inputs, every Kraus matrix commutes with every probe projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kraus-scalar-on-component"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_scalar_on_component"),
                H("kraus scalar on component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For every Kraus index, every probe index, and every vector in its component span, the Kraus action equals a scalar times that vector. The scalar is the unit probe expectation of that Kraus matrix. No finiteness assumption is imposed on the probe family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("channel-component-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.channel_component_scalar"),
                H("channel component scalar"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("Every canonical completely positive trace-preserving channel satisfying the probability equations has a rectangular finite Kraus representation whose normalization and scalar action on every component are proved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("connected-probability-preserving-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity"),
                H("connected probability preserving identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("If the unit probe family spans the full space and every pair belongs to the same component, its probability-preserving Kraus channel equals identity on every complex matrix. Every Kraus matrix is a scalar identity. A probe index and an ambient basis index explicitly provide the nonempty interfaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("component-stinespring-form"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.component_stinespring_form"),
                H("component stinespring form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For each component the finite environment coefficients have squared norm one. Every vector in the component maps to its original system coordinates multiplied by the same environment coefficients. The coordinates are the actual Kraus Stinespring coordinates."))),
                DescribeRole.Theorem))));
}
