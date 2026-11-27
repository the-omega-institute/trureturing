using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class BaseChangeLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Change Level", H("Base Change Level"),
        Blocks(
            Paragraph(Text("Tame levels; matching of unit functions at principal congruence level, keeping unramified places maximal.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel.exists_baseChange_level"),
                H("exists_baseChange_level"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a step, σ ≠ 1 and H open: there are levels K_u ≤ GL_n(O_u) over E', maximal above IsStepUnramifiedAt places w with K_w ≤ H, pulling back into H; each level L above S is open, σ-stable, satisfies CocyclesSplit, and its indicators form a IsMatchingPairAbove.")))))));
}
