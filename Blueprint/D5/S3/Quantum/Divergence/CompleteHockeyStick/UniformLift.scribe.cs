using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.CompleteHockeyStick;

internal sealed class UniformLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full Kraus-product span gives an operator-norm bound on lifts that is independent of the reference dimension.",
        H("Uniform complementary compression lifts"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("matrix-reindex-operator-norm"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.norm_reindex"),
            H("Norm under simultaneous reindexing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("The Euclidean coordinate permutation is unitary, so conjugation by it preserves the operator norm."))),
            DescribeRole.Theorem),
          Describe.Lean(
            DescribeId.Create("reference-output-order"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.referenceOutputOrder"),
            H("Reference-first tensor order"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("The permutation moves the reference before the output and keeps the environment index last."))),
            DescribeRole.Definition),
          Describe.Lean(
            DescribeId.Create("amplified-complement-compression"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.amplifiedComplementCompression"),
            H("Amplified complementary compression"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("The amplified dilation compresses a joint reference and environment observable with identity on the output."))),
            DescribeRole.Definition),
          Describe.Lean(
            DescribeId.Create("full-span-complement-lift"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.exists_uniform_complement_lift_of_full_span"),
            H("Dimension-independent lift"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("The compression sends environment matrix units to the Kraus products. When those products span the input matrix algebra, choose a lift of each input matrix unit. At every reference dimension each coefficient block of an input contraction has norm at most one. The sum of the norms of the fixed lifts, enlarged to at least one, bounds the norm of the amplified lift."))),
            DescribeRole.Theorem))));
}
