using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;
internal sealed class DoubleStarNativeAllSlotsFastDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Six strict original cosine inequalities obtained by finite Gram permutations for the three local families.", H("DoubleStarNativeAllSlotsFast"), Blocks(
Paragraph(Text("Six strict original cosine inequalities obtained by finite Gram permutations for the three local families.")),
Paragraph(Text("These are exact local real inequalities only. Physical realization, seed-parameter existence, face identifications, compatible global gluing, boundary angle budgets and a global cap remain outside these statements. No general CFMP open problem is claimed solved.")),
Describe.Lean(DescribeId.Create("nativestrictsix-of-det-neg"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast.nativeStrictSix_of_det_neg"), H("nativeStrictSix of det neg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("first-native-all-slots"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast.first_native_all_slots"), H("first native all slots"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("middle-native-all-slots"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast.middle_native_all_slots"), H("middle native all slots"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("last-native-all-slots"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast.last_native_all_slots"), H("last native all slots"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem))));
}
