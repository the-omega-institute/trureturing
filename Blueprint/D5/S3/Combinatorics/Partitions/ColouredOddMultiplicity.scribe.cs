using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;
internal sealed class ColouredOddMultiplicityDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Coloured odd occupations and multiplicity partitions", H("Coloured odd multiplicity"), Blocks(
 Paragraph(Text("An occupation assigns a nonnegative integer to each colour and mode. Mode n contributes the positive odd weight 2n+1. Forgetting colours gives an ordinary partition; at each occurring part, its multiplicity is allocated among the finite colour set by a weak composition.")),
 Paragraph(Text("Conversely, every allocation at an odd part k contributes the corresponding exponents at mode k/2. Oddness makes this mode recovery injective. Counting each part and each colour proves both inverse laws, including the empty partition and the empty colour set.")),
 Paragraph(Text("The finite count is the coefficient of the weighted partition GenFun. At each positive odd part k, its local factor has coefficient multichoose(r,N/k) when k divides N and zero otherwise. Reindexing the positive part and positive multiplicity factors yields the formal product of (1-X^(2n+1))^(-r), including rank zero and degree zero.")),
 Describe.Lean(DescribeId.Create("coloured-odd-multiplicity-count"), DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.card_colouredFiber"),
 H("Independent finite partition count"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
 Blocks(Paragraph(Text("For every colour count r and grade N, the cardinal of the weighted occupation fibre equals the sum over partitions of N of the product of multichoose(r,m) for each occurring odd part of multiplicity m, with factor zero at an even part. The count is defined by this finite partition sum."))), DescribeRole.Theorem))));
}
