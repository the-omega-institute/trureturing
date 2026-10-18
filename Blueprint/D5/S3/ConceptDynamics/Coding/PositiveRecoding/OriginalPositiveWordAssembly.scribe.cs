using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class OriginalPositiveWordAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the positive word on the original finite presentation.",
        H("Construct the positive word on the original finite presentation"),
        Blocks(
            Paragraph(Text("positive_word constructs a Word from the actual (a+b+1)-fold full outgoing tower, the actual numbered full-out/response relabeling and the constructed response positive word. The internal induction proves that the input full-out tower has no incoming stages. Every letter and intermediate endpoint lies in TypedPositiveSplitWord.Word, whose constructors contain neither arbitrary history homeomorphisms nor inverse letters.")),
            Paragraph(Text("For finite V,E with DecidableEq V,E, discrete topological E, an essential graph G, TablePair G G a b c d and SameTableConjugacy pair, the word has (a+b+1)+2*((a+c)+(b+d+1)) positive letters. For every original history x, S.forward x equals time G (-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ)) applied to w.eval x. Both the count and the signed correction are conclusions of the construction. No original h is fixed here, and the arbitrary radii and the supplied same-table conjugacy remain explicit.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Lean(DescribeId.Create("positive-recoding-originalpositivewordassembly-positive-word"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/OriginalPositiveWordAssembly.positive_word"), H("positive_word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A finite word on the ORIGINAL graph. Its input is the actual q-fold full outgoing tower, then the actual finite numbered identification, then the constructed response word. No inverse, time, U or arbitrary-history-map leaf is introduced. Both the letter count and the correction are derived."))), DescribeRole.Theorem))));
}
