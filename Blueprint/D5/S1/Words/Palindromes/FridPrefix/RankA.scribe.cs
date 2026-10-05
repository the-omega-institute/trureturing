using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class RankADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal deterministic rank table has width 6, initial state 0, and 99 rows", H("The literal deterministic rank table has width 6, initial state 0, and 99 rows"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-ranka-ranka"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/RankA.rankA"),
                H("rankA"), StatementSource.FromAuthor(Disp(Seq(F.Id("rankA"),Colon,F.Id("ChunkRank")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal deterministic rank table has width 6, initial state 0, and 99 rows. State 98 is its dead state. transitions and weights are the two arrays printed in Lean; a numeric six-bit chunk labels each column."))), DescribeRole.Definition))));

}
