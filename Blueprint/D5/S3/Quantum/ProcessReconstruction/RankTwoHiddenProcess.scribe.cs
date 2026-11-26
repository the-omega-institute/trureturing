using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class RankTwoHiddenProcessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess";
    private static readonly LibraryNoteRef Schumacher =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/schumacher2004reversible");

    private static readonly LibraryNoteRef Haapasalo =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/haapasalo2012extremal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a register of at least two qubits, the minimal Kraus rank for ambiguity from all proper output channels is two.",
        H("Kraus Rank and Hidden Process Correlations"),
        Blocks(
            Describe.Lean(DescribeId.Create("rank-one-identification"),
                DeclarationHandle.Create(Module + ".one_kraus_eq_of_proper_output_eq"),
                H("Proper-output reconstruction for rank-one channels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Schumacher, Haapasalo),
                Blocks(Paragraph(Text(
                    "A single Kraus operator for a trace-preserving channel on an equal "
                    + "finite input and output basis is unitary. For a register with at least "
                    + "two sites, the proper output channels include all single-site outputs. "
                    + "Their equality determines the global channel when both channels have a single Kraus operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-two-ambiguity"),
                DeclarationHandle.Create(Module + ".rank_two_ambiguity"),
                H("Rank-two channels with identical complete proper outputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Schumacher),
                Blocks(
                    Paragraph(Text(
                        "Two unital channels retain the same two diagonal blocks, and one "
                        + "channel changes the sign of the coherence between the all-zero "
                        + "and all-one basis words. A proper partial trace kills both of the "
                        + "matrix units carrying the difference for every input matrix. The proper output channels remain equal under every finite reference amplification.")),
                    Paragraph(Text(
                        "The balanced superposition of those words gives orthogonal outputs, "
                        + "attaining unhalved diamond distance two. Another pure input gives "
                        + "an output of rank two for each channel, so each two-Kraus "
                        + "representation is minimal."))),
                DescribeRole.Theorem))));
}
