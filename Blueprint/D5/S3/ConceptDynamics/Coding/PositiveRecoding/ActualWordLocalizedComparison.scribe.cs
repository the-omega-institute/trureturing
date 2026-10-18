using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualWordLocalizedComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rectangular localized cochain equals the same actual positive-word gyration modulo three.",
        H("The rectangular localized cochain equals the same actual positive-word gyration modulo three"),
        Blocks(
            Paragraph(Text("The passage to the arithmetic cochain is coefficientwise localization of the actual positive factors with their chart corrections. The same d, word, old/next edge bijections and forward-time convention occur on both sides of the comparison.")),
            Describe.Lean(
                DescribeId.Create("actualwordlocalizedcomparison-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison.localizedCochain"),
                H("Localize the literal factors and retain the charts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a natural d with NeZero d and hd : three divides d. A relabel contributes its actual gyration reduced by ZMod.castHom hd to ZMod 3. A positive leaf contributes negative reduced old-chart gyration, dyadicGyration of the literal R and S mapped first to the integers and then to GyrationDyadic, and positive reduced next-chart gyration. Composition adds. R has size n by m and S size m by n, with no nonempty-fiber, rank, square or determinant assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualwordlocalizedcomparison-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison.localizedCochain_eq"),
                H("The localized sum is the same actual word invariant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary literal endpoints F,H, every Word F H and every nonzero d divisible by three, localizedCochain d hd w equals the reduction of (wordMap w).gyration d. The positive case applies dyadicGyration_nonnegative to the same nonnegative rectangular factors, inside the two genuine chart terms. The composition case uses the actual wordMap_comp and gyration_comp. This is a source-level comparison of two independently defined readouts; it does not define a matrix invariant to be the desired history value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordlocalizedcomparison-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison.corrected_localized_word"),
                H("Restore the full signed history action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given w : Word F F, s : integers, h : Hist F equivalent to itself, ht commuting with all integer times, and hh : for every x, h x = time F.graph s (w.eval x), the reduced historyGyration equals localizedCochain d hd w plus card(Orbit F d) times s in ZMod 3. The proof combines time_corrected_word with localizedCochain_eq and word_gyration. It does not yet identify the word endpoint map with the native beam representation; the preserved original application supplies that independent equality and both of its factors."))),
                DescribeRole.Theorem),
            Paragraph(Text("The full native-image and SAME-character application is recorded in the ActualWordEnumeratedLoop owner narrative. The preserved original application supplies the independent endpoint and signed-cut identifications before applying corrected_localized_word; this owner does not infer them from the cochain equality.")))));
}
