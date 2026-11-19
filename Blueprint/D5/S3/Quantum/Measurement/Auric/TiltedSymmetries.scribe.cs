using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class TiltedSymmetriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realization of each symmetry conjugate",
        H("Realization of each symmetry conjugate"),
        Blocks(Describe.Lean(
            DescribeId.Create("realizes-phase-permuted-tilt"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/TiltedSymmetries.realizes_phase_permuted_tilt"),
            H("Realization of each symmetry conjugate"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Conjugating the tilted measurement and its conditional unitaries and relabeling the outputs implements every phase and permutation term using the original register."))),
            DescribeRole.Theorem))));
}
