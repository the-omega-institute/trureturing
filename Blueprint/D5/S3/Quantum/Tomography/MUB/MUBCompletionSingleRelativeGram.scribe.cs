using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;
internal sealed class MUBCompletionSingleRelativeGramDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
  "A fixed-edge mutually unbiased double completion yields one relative Gram system.", H("MUB Completion Single Relative Gram"), Blocks(
   Describe.Lean(DescribeId.Create("double-completion-single-relative-gram-system"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/MUBCompletionSingleRelativeGram.doubleCompletion_yields_singleRelativeGramSystem"), H("Single relative Gram system"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A fixed-edge mutually unbiased double completion yields a scaled-Hadamard relative Gram that recovers both second factors."))), DescribeRole.Theorem),
   Describe.Lean(DescribeId.Create("double-completion-single-relative-gram-system-six-dimensional"), DeclarationHandle.Create("D5/S3/Quantum/Tomography/MUB/MUBCompletionSingleRelativeGram.doubleCompletion_yields_singleRelativeGramSystem_six"), H("Dimension-six relative Gram system"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The necessary relative-Gram equations specialize to the dimension-six carrier."))), DescribeRole.Theorem)
 )));
}
