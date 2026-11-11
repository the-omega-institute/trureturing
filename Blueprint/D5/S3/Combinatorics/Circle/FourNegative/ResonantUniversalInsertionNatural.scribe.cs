using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative;

internal sealed class ResonantUniversalInsertionNaturalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict natural prefixes for the resonant universal insertion",
        H("Adaptive low-row orientation above the boundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("resonant-natural-prefix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionNatural.resonant_target_word_natural_prefix_strict"),
                H("Every natural target prefix stays in both strips"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the strict boundary inequality ell<k, the adaptive orientation chosen from the source prefix keeps every natural take of the lifted target word inside the first and second target rectangles. The proof handles prefixes inside a block and across complete blocks, while retaining the exact source permutation and endpoint hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("resonant-natural-word"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionNatural.resonant_target_word_of_source_strict"),
                H("Strict adaptive target word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every legal resonant source word with ell<k admits the adaptive physical lift with one occurrence of every target label, zero total in both coordinates, and all natural prefixes in the target strips."))),
                DescribeRole.Theorem)), []));
}
