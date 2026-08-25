using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;
internal sealed class MinimalTargetDistillationDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Exact target distillation removes defects without over-separation.",H("Minimal Target Distillation"),Blocks(Describe.Lean(DescribeId.Create("exact-distillation-is-zero-defect-and-zero-over"),DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/MinimalTargetDistillation.exact_distillation_iff_defect_over_empty"),H("Exact distillation is characterized by two empty residuals"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("ExactTargetDistillation compares candidate and target completion fibers; defectRelation and OverResidual remain the canonical residuals.")),Paragraph(Text("Exactness forces both residuals empty, while their emptiness recovers both coordinate equalities for every pair."))),DescribeRole.Theorem))));
 private static Formula Formula(){var c=F.Id("current");var t=F.Id("target");var a=F.Id("added");var j=Call("conceptJoin",c,a);return Disp(Seq(Call("ExactTargetDistillation",c,t,a),Sp,Iff,Sp,Open,Call("defectRelation",j,t),Sp,Eq,Sp,Emptyset,Close,Sp,Land,Sp,Open,Call("OverResidual",c,t,a),Sp,Eq,Sp,Emptyset,Close,Dot));}
}
