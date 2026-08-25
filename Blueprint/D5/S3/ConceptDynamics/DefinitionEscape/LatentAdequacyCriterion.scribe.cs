using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;
internal sealed class LatentAdequacyCriterionDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Target adequacy binds canonical recovery to join strictness.",H("Latent Adequacy Criterion"),Blocks(Describe.Lean(DescribeId.Create("latent-join-strictness-characterizes-inadequacy"),DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion.latent_join_strict_iff_inadequate"),H("Joining the target is strict exactly under inadequacy"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("StrictRefinement and conceptJoin are the canonical carriers, while adequacy is the existing Refines recovery predicate.")),Paragraph(Text("Recoverability prevents strictness through the universal join factor; inadequacy supplies the missing reverse factor."))),DescribeRole.Theorem))));
 private static Formula Formula(){var l=F.Id("latent");var t=F.Id("target");return Disp(Seq(Call("StrictRefinement",l,Call("conceptJoin",l,t)),Sp,Iff,Sp,Neg,Sp,Call("TargetAdequate",l,t),Dot));}
}
