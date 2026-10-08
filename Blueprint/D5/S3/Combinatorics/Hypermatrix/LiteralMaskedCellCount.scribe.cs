using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypermatrix;

internal sealed class LiteralMaskedCellCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cell cardinality", H("Exact cell cardinality"),
        Blocks(
            Describe.Lean(DescribeId.Create("literalsolutions"),
                DeclarationHandle.Create(Prefix + "LiteralSolutions"), H("Literal masked-cell equations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each eligible or ineligible permutation pair sigma,pi, assign elements of F to the disjoint inversion coordinates. Require the actual product entries sum over b of cellA(r,b) cellB(b,j), using castSucc for the first face and succ for the second, to vanish at both original forbidden row thresholds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-cell-count-original-masks"),
                DeclarationHandle.Create(Prefix + "literal_cell_count_original_masks"), H("Exact cell cardinality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let F be any finite field and k at least one. Let lambda and mu on Fin(k) be antitone, with mu(j) at most lambda(j), lambda(j) at most k minus j, and mu(j) strictly less than k minus j. For every permutation pair sigma of Fin(k plus one) and pi of Fin(k), the number of literal masked coordinate assignments is q to the natural value of the actual integer exponent E if the pair is Eligible at thresholds k plus one minus lambda and k plus one minus mu, and zero otherwise. Here q is the cardinality of F, and E is the existing inversion count minus the two actual forbidden counts. Each forbidden equation has a distinct coefficient-one final variable; an explicit acyclic order yields unique elimination and leaves exactly the free coordinates counted by the exponent. No specialized values are substituted for generic forbidden counts."))), DescribeRole.Theorem)
        ), []));
}
