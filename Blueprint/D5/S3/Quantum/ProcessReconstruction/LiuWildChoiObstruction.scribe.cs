using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class LiuWildChoiObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform exponential Choi conditional mutual information decay permits maximal diamond distance under identical proper-window data.",
        H("Diamond Reconstruction Limits under Choi Conditional Mutual Information Decay"),
        Blocks(
            Describe.Lean(DescribeId.Create("choi-diamond-separation-with-cmi-decay"),
                DeclarationHandle.Create(Module + ".uniform_obstruction"),
                H("Identical proper Choi windows and maximal diamond distance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(
                    Paragraph(Text(
                        "Pair each input reference with its corresponding output site. "
                        + "On any register of at least two qubits, the two unital rank-two "
                        + "channels have identical normalized Choi marginals on every "
                        + "proper paired window. The trace norm of their normalized Choi difference is 4/2ⁿ and "
                        + "their unhalved diamond distance is 2.")),
                    Paragraph(Text(
                        "Each paired marginal has rank at most three and large overlap "
                        + "with a product of Bell states. These properties give a uniform "
                        + "exponential conditional mutual information bound in nats in the size "
                        + "of the middle region."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-paired-data-minimax"),
                DeclarationHandle.Create(Module + ".paired_data_minimax"),
                H("Worst-case diamond reconstruction error from proper windows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Any reconstruction function of the exact proper paired marginals "
                    + "must return the same estimate for the two channels. Its unhalved "
                    + "diamond error is at least 1 on one of them. The uniform conditional "
                    + "mutual information bound puts both channels in the class used in "
                    + "Liu and Wild's local tomography guarantee."))),
                DescribeRole.Theorem))));
}
