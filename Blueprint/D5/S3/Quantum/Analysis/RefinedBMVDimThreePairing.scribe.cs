using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVDimThreePairingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV pairing on three matrix indices",
        H("The refined BMV pairing on three matrix indices"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-three-index-pairing"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVDimThreePairing.walk_nonneg"),
            H("Nonnegativity of the walk sum under the geometric-mean pairing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "Reversal combines the two orientations of the three-index triangle into its real part. The positive semidefinite entry bound and the arithmetic-geometric mean inequality pair the six repeated-index terms without dividing by any matrix entries."))),
            DescribeRole.Theorem))));
}
