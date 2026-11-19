using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class RepeatedPairModularTablesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularTables." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete residue tables at three and five", H("Complete residue tables at three and five"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged.")),
            Item("three-table", "three_table", "All three tail residues", "Exactly residue one is excluded; zero discriminant remains allowed."),
            Item("five-table", "five_table", "All five tail residues", "Exactly residues three and four are excluded."),
            Item("actual-three", "actual_three", "Actual arbitrary-tail prime-three consumer", "The table applies separately to every remaining exponent."),
            Item("actual-five", "actual_five", "Actual arbitrary-tail prime-five consumer", "The complete table is used as a necessary graph obstruction, never as a sufficient integrality claim.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularResidues"))]));
}
