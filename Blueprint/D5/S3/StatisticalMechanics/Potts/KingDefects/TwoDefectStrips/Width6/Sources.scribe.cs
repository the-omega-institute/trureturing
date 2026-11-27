using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6;
internal sealed class SourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical source rows with valid residual budgets.", H("Width-six source index"), Blocks(
            Describe.Remark(DescribeId.Create("sources"), DeclarationHandle.Create(Prefix + "sources"),
                H("Valid sources"), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The type is Fin 313 -> Data.Row x Fin 3. The entries are exactly the canonical six-position rows paired with residual budgets d for which the horizontal defect count is at most 2-d. Certificate.canonical_successors proves reconstruction from the row index and budget.")))),
            Describe.Remark(DescribeId.Create("source-index"), DeclarationHandle.Create(Prefix + "sourceIndex"),
                H("Source lookup"), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The type is Fin 187 -> Fin 3 -> Fin 313. At every valid row and residual budget, this lookup selects their pair in sources; values at invalid pairs are immaterial. Certificate.canonical_successors pins the lookup on the valid domain.")))))));
}
