using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;
internal sealed class DoubleStarNativeGramDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Negative native hyperideal Gram determinants for the three local transition families.", H("DoubleStarNativeGram"), Blocks(
Paragraph(Text("Negative native hyperideal Gram determinants for the three local transition families.")),
Paragraph(Text("These are exact local real inequalities only. Physical realization, seed-parameter existence, face identifications, compatible global gluing, boundary angle budgets and a global cap remain outside these statements. No general CFMP open problem is claimed solved.")),
Describe.Lean(DescribeId.Create("chosenopp-native-gram-negative"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.chosenOpp_native_gram_negative"), H("chosenOpp native gram negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("first-native-gram-negative"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative"), H("first native gram negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("middle-native-gram-negative"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative"), H("middle native gram negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("last-native-gram-negative"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative"), H("last native gram negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem))));
}
