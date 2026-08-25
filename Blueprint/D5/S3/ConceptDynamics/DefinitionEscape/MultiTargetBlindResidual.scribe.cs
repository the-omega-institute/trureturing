using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;
internal sealed class MultiTargetBlindResidualDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("A joint target's blind residual is the union of its components' residuals.",H("Multi-Target Blind Residual"),Blocks(Describe.Lean(DescribeId.Create("family-blind-residual-is-component-union"),DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/MultiTargetBlindResidual.familyBlindResidual_eq_iUnion"),H("The joint blind residual is the component union"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The dependent joint target uses the existing blindResidual carrier and common joint kernel.")),Paragraph(Text("A joint target differs exactly when one component differs, yielding the indexed-union equality."))),DescribeRole.Theorem))));
 private static Formula Formula(){var g=F.Id("Gamma");var c=F.Id("current");var t=F.Id("targets");return Disp(Seq(Call("FamilyBlindResidual",g,c,t),Sp,Eq,Sp,Call("iUnion",F.Id("index"),Call("blindResidual",g,c,Call("targets",F.Id("index")))),Dot));}
}
