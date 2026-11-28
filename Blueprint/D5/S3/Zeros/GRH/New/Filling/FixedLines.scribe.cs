using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class FixedLinesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed Lines", H("Fixed Lines"),
        Blocks(
            Paragraph(Text("A group Z between K(g) and K for which Level.floorZeroForm Z, divided by the measure of Z, is smaller than for K by b^(6|κ|) for each given place above q₀ where a frame vector is fixed.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/FixedLines.exists_intermediateGroup_lines"),
                H("exists_intermediateGroup_lines"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Sg be a set of chosen places above q₀, and 1/g integral off T. Some group K(g) ≤ Z ≤ K contains k_T whenever k reduces into Filling.fixingSet Sg d, and kk(Z)·M(K)·b^(6|κ||Sg|) ≤ kk(K)·M(Z), kk = Level.floorZeroForm, M = Level.groupMeasure.")))))));
}
