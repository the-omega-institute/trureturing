using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreUpperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original local cell proof", H("The original local cell proof"),
        Blocks(Paragraph(Text("Cell weights, all actual path constraints and across-cell constraints are distinct data. The received proofs bound a cell, classify tight cells and bound three-cell blocks with one or two selected hubs. These local lemmas alone do not assert a graph parameter or an all-length assembly.")),
            Node("Cell", "Cell", "Exact declaration: structure Cell.", DescribeRole.Definition),
            Node("Cell.weight", "Cell.weight", "Exact declaration: def Cell.weight (cell : Cell) : Nat.", DescribeRole.Definition),
            Node("Valid", "Valid", "Exact declaration: def Valid (cell : Cell) (evenHub oddHub : Nat) : Prop.", DescribeRole.Definition),
            Node("Across", "Across", "Exact declaration: def Across (first second : Cell) : Prop.", DescribeRole.Definition),
            Node("cell_cap", "cell cap", "Exact declaration: theorem cell_cap (cell : Cell) (evenHub oddHub : Nat) (hvalid : Valid cell evenHub oddHub) : cell.weight ≤ 3.", DescribeRole.Theorem),
            Node("one_hub_tight", "one hub tight", "Exact declaration: theorem one_hub_tight (cell : Cell) (hvalid : Valid cell 1 0) (htight : cell.weight = 3) : (cell.cut = 0 ∧ cell.leafLeft = 1 ∧ cell.leafRight = 1 ∧ cell.highLeft = 0 ∧ cell.highRight = 1) ∨ (cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.highLeft = 1 ∧ cell.highRight + cell.leafRight = 1).", DescribeRole.Theorem),
            Node("two_hub_tight", "two hub tight", "Exact declaration: theorem two_hub_tight (cell : Cell) (hvalid : Valid cell 1 1) (htight : cell.weight = 3) : cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.leafRight = 0 ∧ cell.highLeft = 1 ∧ cell.highRight = 1.", DescribeRole.Theorem),
            Node("one_hub_next_cut", "one hub next cut", "Exact declaration: theorem one_hub_next_cut (first second : Cell) (hfirst : Valid first 1 0) (hsecond : Valid second 1 0) (htightFirst : first.weight = 3) (htightSecond : second.weight = 3) (hacross : Across first second) : second.cut = 0.", DescribeRole.Theorem),
            Node("one_hub_block", "one hub block", "Exact declaration: theorem one_hub_block (first middle last : Cell) (hfirst : Valid first 1 0) (hmiddle : Valid middle 1 0) (hlast : Valid last 1 0) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) (hhub : middle.leafLeft + last.leafLeft + 1 ≤ 2) : 3 + first.weight + middle.weight + last.weight + 1 ≤ 12.", DescribeRole.Theorem),
            Node("two_hub_block", "two hub block", "Exact declaration: theorem two_hub_block (first middle last : Cell) (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1) (hlast : Valid last 1 1) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) : 3 + first.weight + middle.weight + last.weight + 2 ≤ 13 ∧ (3 + first.weight + middle.weight + last.weight + 2 = 13 → first.weight = 3 ∧ middle.weight = 2 ∧ last.weight = 3).", DescribeRole.Theorem)), []));
}
