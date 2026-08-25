using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;
internal sealed class InverseLimitCompletionDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("A refinement tower matches states to its threads iff separating and complete.",H("Inverse Limit Completion"),Blocks(Describe.Lean(DescribeId.Create("state-thread-bijective-iff-complete-separating"),DeclarationHandle.Create("D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates"),H("States correspond bijectively to threads exactly under completeness and separation"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("stateThread maps each state to its compatible values at every refinement stage. ThreadComplete is its surjectivity and SeparatesStates is all-stage injectivity.")),Paragraph(Text("The injectivity criterion paired with thread completeness gives the bijection biconditional."))),DescribeRole.Theorem))));
 private static Formula Formula(){var s=F.Id("system");return Disp(Seq(Call("Bijective",Call("stateThread",s)),Sp,Iff,Sp,Open,Call("ThreadComplete",s),Sp,Land,Sp,Call("SeparatesStates",s),Close,Dot));}
}
