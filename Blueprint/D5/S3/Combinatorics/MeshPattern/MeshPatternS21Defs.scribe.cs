using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21DefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mesh patterns 123 and 321 with shading R = {0,1,2} squared together with {(3,3)} define two occurrence statistics on permutations.",
        H("The Mesh Pattern Pair S21"),
        Blocks(
            Node("mesh-pattern-s21defs-shaded", "The common shading", "Shaded",
                "A cell with column c and row r is shaded when both c and r are at most two, or when both equal three. Columns and rows are counted from zero.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-column", "The column of an additional position", "column",
                "Relative to three selected positions i, j and k, the column of a position l is the number of selected positions strictly less than l.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-row", "The row of an additional value", "row",
                "Relative to three selected values a, b and c, the row of a value x is the number of selected values strictly less than x.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-isoccurrence", "Mesh occurrences", "IsOccurrence",
                "A triple of strictly increasing positions within a word is an occurrence when its values are strictly increasing for the 123 pattern, or strictly decreasing for the 321 pattern, and every other position has its point outside the common shading. Positions are counted from zero.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-occ", "The occurrence count", "occ",
                "The occurrence count is the cardinality of the set of triples realizing the chosen mesh pattern. The Boolean parameter selects 123 when true and 321 when false.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-joint", "Joint occurrence classes", "joint",
                "For nonnegative integers n, k and l, the joint class consists of the permutations of one through n having exactly k occurrences of the shaded 123 pattern and exactly l occurrences of the shaded 321 pattern.", DescribeRole.Definition),
            Node("mesh-pattern-s21defs-claim", "Joint symmetry", "claim",
                "For all nonnegative integers n, k and l, the joint class with occurrence counts k and l has the same cardinality as the joint class with occurrence counts l and k.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
