using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOptimalInternalLatinDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An optimal internal extension of lifted ternary lines determines one Latin square on each row.",
        H("Latin Squares of Optimal Internal Extensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latin-point"),
                DeclarationHandle.Create(Module + ".latinPoint"),
                H("The triple attached to a Latin-square cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a fixed row, use the two cell indices as labels in residue classes zero and one. "
                    + "The entry at that cell supplies the label in residue class two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-latin-of-optimal-family"),
                DeclarationHandle.Create(Module + ".exists_latin_of_optimal_family"),
                H("Every optimal family comes from Latin squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The internal family has exactly as many ordered slots as there are different-residue ordered pairs within rows. "
                    + "Saturation makes every added triple meet all three residues. "
                    + "The unique completions of pairs in each row give the row and column permutation laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latin-assignment-injective"),
                DeclarationHandle.Create(Module + ".latin_assignment_injective"),
                H("The unordered family determines the squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The residue of each point determines its slot even after forgetting the order of the triple. "
                    + "The row and the two cell indices determine the third label, so equality of the families gives equality of the entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optimal-family-of-latin"),
                DeclarationHandle.Create(Module + ".optimal_family_of_latin"),
                H("Every assignment gives an optimal extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The permutation laws give unique completion for any two residue classes within a row. "
                    + "The construction retains the mixed triples and satisfies the residue criterion for dimension d plus one. "
                    + "There is one new triple for each cell in each row."))),
                DescribeRole.Theorem))));
}
