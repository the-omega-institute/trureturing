using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BinaryRandomUnitaryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "A unitary decoder maximizes binary random-unitary recovery fidelity.",
            "evidence-not-specified-by-formal-manifest"),
        H("Unitary recovery for a binary random-unitary channel"),
        Blocks(
            Describe.Lean(DescribeId.Create("diagonalize"), DeclarationHandle.Create(Module + ".unitary_diagonalize"),
                H("A unitary eigenbasis with unit-modulus diagonal entries"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every unitary on Fin d is diagonal in a unitary eigenbasis. The squared modulus of each diagonal entry is one by unitarity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-optimum"), DeclarationHandle.Create(Module + ".binary_unitary_optimal"),
                H("Attainment against all CPTP decoders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Resource/karimipourbenattifloreanini2020quasiinversion"),
                    LibraryNoteRef.Create("D5/L/Resource/shahbeigietal2021quasiinversion")),
                Blocks(
                    Paragraph(Text(
                        "For each natural d > 0, each pair of real weights p,q ≥ 0 with p+q = 1, and each pair of code unitaries U,V, "
                        + "there exists a unitary Z such that every actual CPTP decoder D has recovery score at most that of the actual CPTP conjugation by Z. "
                        + "Both zero-weight endpoints are included. The objective is the squared canonical entanglement fidelity at I/d in a single use with an untouched reference.")),
                    Paragraph(Text("The change of basis uses the relative unitary, with the superscript denoting the complex adjoint.")),
                    new DocumentBlock.DisplayFormula(Equal(F.Id("W"),
                        Seq(new Formula.Power(F.Id("U"), Star), F.Id("V")))),
                    Paragraph(Text(
                        "In a unitary eigenbasis its phases give the diagonal binary channel. The proof transports the weighted Kraus trace expression by left and right unitary factors, then transports an actual optimizing diagonal decoder back to the original basis.")),
                    Paragraph(Text(
                        "The cited quasi-inversion results provide context for arbitrary qubit channels, orthogonal mixtures in arbitrary dimension, and commuting qutrit mixtures."))),
                DescribeRole.Theorem))));
}
