using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalPhysicalTargetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-law states and their coherent record",
        H("Fixed-law states and their coherent record"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("input-record-law"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.input_recordLaw"),
                H("The Born law of the normalized input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An admissible state is P/r for a rank-r Hermitian projection with fiber trace r q_j and constant diagonal on each fiber. At positive r its record probabilities equal q_j. An empty fiber has no diagonal entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-of-gain"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.physical_of_gain"),
                H("Transfer of all three extrema to one state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(
                    Paragraph(Text("At fixed original law q, an attained pinching gain B/r gives mutual information H(q) + B/r and conditional entropy −B/r on the same state. The same pointwise identities compare these quantities on every admissible state and give the opposite inequality for the conditional entropy."))),
                DescribeRole.Theorem))));
}
