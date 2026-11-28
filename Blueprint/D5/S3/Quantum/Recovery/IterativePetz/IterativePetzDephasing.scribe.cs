using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.IterativePetz;

internal sealed class IterativePetzDephasingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/lautenbacher2026iterativepetz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact phase-aligned qubit update and the asymptotic bias of iterative Petz recovery.",
        H("Iterative Petz recovery under single-axis dephasing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("principal-petz-update"),
                DeclarationHandle.Create(Module + "matrixStep_eq_principal_petz"),
                H("Petz update in the phase-aligned qubit slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The explicit real matrix update uses the principal square root of the "
                    + "reference and the inverse principal square root of its dephased image. "
                    + "The off-diagonal and diagonal entries yield the two coordinate updates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-target-limit"),
                DeclarationHandle.Create(Module + "pure_target_limit"),
                H("Pure limit with a strict axial fidelity deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a coherence multiplier strictly between zero and one, the orbit "
                    + "from the unbiased first recovery converges to the unit Bloch circle. "
                    + "At nonzero latitude the strict loss in absolute axial component at "
                    + "the second recovery gives a persistent fidelity deficit. An equatorial "
                    + "target is recovered in the limit."))),
                DescribeRole.Theorem))));
}
