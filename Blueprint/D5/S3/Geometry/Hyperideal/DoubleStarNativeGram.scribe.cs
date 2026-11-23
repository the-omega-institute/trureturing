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
Describe.Lean(DescribeId.Create("last-native-gram-negative"), DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative"), H("last native gram negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion."))), DescribeRole.Theorem),
new DocumentBlock.Section(H("Six original cosine bounds for the double star"), Blocks(
    Paragraph(
        Text("For a real tuple (r,a,b,o,c,d) in edge order (12,13,14,34,24,23), write Q(r,a,b,o,c,d) = N(r,a,b,o,c,d) / (sqrt(D1(r,a,d)) * sqrt(D2(r,b,c))). The signed Gram matrix and the functions N, D1 and D2 are those of "),
        Ref("D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface"),
        Text(".")),
    Paragraph(
        Text("Assume r, a, b, o, c and d are each strictly greater than 1 and det(gram(r,a,b,o,c,d)) < 0. Then −1 < Q < 1 for each of the six argument tuples, in order (r,a,b,o,c,d), (a,r,b,c,o,d), (b,r,a,d,o,c), (o,a,d,r,c,b), (c,r,d,a,o,b) and (d,r,c,b,o,a). Apply the determinant-to-cosines direction of "),
        Ref("D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg"),
        Text(".")),
    Paragraph(
        Text("For every real x with 12 ≤ x ≤ 20, the six inequalities hold for each tuple below. In every tuple r = x, so r > 1, and all four fixed entries exceed 1. The proved opposite-root lower bounds supply o > 1, and the corresponding native Gram theorems supply the negative determinant.")),
    Paragraph(
        Text("First family. Use (x,101/100,500,o,101/100,3/2) with o = chosenOpp(x,101/100,3/2,500,101/100). The root satisfies 6 < o < 30, and the native determinant is negative. "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarOpposite.first_exact"),
        Text(", "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative")),
    Paragraph(
        Text("Middle family. Use (x,500,500,o,101/100,101/100) with o = chosenOpp(x,500,101/100,500,101/100). The root satisfies 6 < o < 250, and the native determinant is negative. "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarOpposite.middle_exact"),
        Text(", "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative")),
    Paragraph(
        Text("Last family. Use (x,500,101/100,o,101/100,101/100) with o = chosenOpp(x,500,101/100,101/100,101/100). The root satisfies 2 < o < 6, and the native determinant is negative. "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarOpposite.last_exact"),
        Text(", "),
        Ref("D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative")))))));
}
