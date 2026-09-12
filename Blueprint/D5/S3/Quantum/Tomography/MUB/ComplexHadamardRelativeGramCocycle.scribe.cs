using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;
internal sealed class ComplexHadamardRelativeGramCocycleDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
  "Relative Grams of finite complex Hadamards form a scaled transition cocycle.", H("Complex Hadamard Relative Gram Cocycle"), Blocks(
   Describe.Lean(DescribeId.Create("relative-gram-refl"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle.relativeGram_refl"), H("Relative Gram reflexivity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The relative Gram of a complex Hadamard with itself is cardinality times the identity."))), DescribeRole.Theorem),
   Describe.Lean(DescribeId.Create("relative-gram-reverse"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle.relativeGram_reverse"), H("Relative Gram reversal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reversing a relative transition gives its conjugate transpose."))), DescribeRole.Theorem),
   Describe.Lean(DescribeId.Create("relative-gram-cocycle"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle.relativeGram_cocycle"), H("Relative Gram cocycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Relative Grams compose with the finite cardinality scaling law."))), DescribeRole.Theorem),
   Describe.Lean(DescribeId.Create("relative-gram-triangle"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle.relativeGram_triangle"), H("Hadamard triangle composition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Three pairwise relative Grams satisfy every cyclic composition law."))), DescribeRole.Theorem),
   Describe.Lean(DescribeId.Create("four-mub-witness-relative-gram-edges"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle.fourMUBWitness_relativeGram_edges"), H("Four-MUB relative Gram edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every off-diagonal edge of a normalized four-MUB witness is a scaled complex Hadamard and obeys the cocycle law."))), DescribeRole.Theorem)
 )));
}
