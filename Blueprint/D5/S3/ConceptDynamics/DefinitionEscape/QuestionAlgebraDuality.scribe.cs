using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;
internal sealed class QuestionAlgebraDualityDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Effective concept refinement is exactly inclusion of answerable Boolean questions.",H("Question Algebra Duality"),Blocks(Describe.Lean(DescribeId.Create("effective-refinement-is-question-inclusion"),DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality.effective_refinement_iff_question_inclusion"),H("Effective refinement is equivalent to question inclusion"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Effective readouts normalize to attained-coordinate subtypes and reuse AnswerableQuestions.")),Paragraph(Text("Refinement transports every Boolean question; conversely, a coarse-coordinate question reconstructs the required fiber implication."))),DescribeRole.Theorem))));
 private static Formula Formula(){var c=Call("effectiveReadout",F.Id("coarse"));var f=Call("effectiveReadout",F.Id("fine"));return Disp(Seq(Call("Refines",c,f),Sp,Iff,Sp,Call("Subset",Call("AnswerableQuestions",c),Call("AnswerableQuestions",f)),Dot));}
}
