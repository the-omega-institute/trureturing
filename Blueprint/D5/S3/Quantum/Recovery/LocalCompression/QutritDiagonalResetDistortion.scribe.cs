using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class QutritDiagonalResetDistortionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the qutrit Bell source and a plane-preserving diagonal reset, the smaller matched "
        + "probability of any decoder determines an explicit protocol with no larger joint trace distance.",
        H("Sharp trace-distance converse for diagonal-reset qutrit compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qutrit-diagonal-reset-distortion-converse"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetDistortion."
                    + "diagonal_reset_distortion_converse"),
                H("The attenuating decoder attains the matched Rayleigh bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "The source is the normalized qutrit Bell state, with the reference untouched. "
                    + "The encoder and decoder are fixed channels communicating through the qubit. "
                    + "After ordering the retained levels by matched output probability, take x to be the "
                    + "square root of the smaller probability and let N be the corresponding real model block. "
                    + "Entrywise nonnegativity lets each real quadratic test vector be replaced by its "
                    + "coordinatewise absolute value. The arbitrary protocol's matched block then bounds "
                    + "this expectation from above. The trace-zero joint difference bounds each unit-vector "
                    + "expectation by half its trace norm. The explicit decoder and pure reset give N/3 "
                    + "on the matched coordinates and negative semidefinite diagonal losses on their complement. "
                    + "The joint difference is rank-one positive minus positive semidefinite, so its unique "
                    + "positive eigenvalue is half the trace norm. Its eigenvector has matched support, and "
                    + "the moduli of its coordinates give a real unit vector attaining the largest quadratic "
                    + "value of N. The explicit protocol therefore has joint half trace-norm error "
                    + "equal to the largest real Rayleigh value divided by three and at most the "
                    + "error of the original protocol."))),
                DescribeRole.Theorem))));
}
