using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class PartialSwapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/PartialSwap";
    private static readonly LibraryNoteRef Bravyi =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/bravyi2026identitycheck");
    private static readonly LibraryNoteRef Huang =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/huang2024learning");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial SWAP norms track the complete error at each inserted site.",
        H("Partial SWAP estimates for unitary channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("partial-step"),
                DeclarationHandle.Create(Module + ".norm_partial_step"),
                H("Control of one partial SWAP increment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("Conjugating by additional commuting local SWAPs preserves the operator-norm estimate for an increment. The unhalved diamond error of the complete single-output channel bounds that increment."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("input-unitary"),
                DeclarationHandle.Create(Module + ".diamondDistance_precompose_unitary"),
                H("Invariance under unitary precomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("Precomposing both channels with the same input conjugation preserves the diamond distance. Its inverse conjugation transports the reference-amplified optimization in the opposite direction."))),
                DescribeRole.Theorem))));
}
