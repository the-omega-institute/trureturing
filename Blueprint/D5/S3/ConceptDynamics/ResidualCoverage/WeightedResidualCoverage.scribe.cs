using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ResidualCoverage;
internal sealed class WeightedResidualCoverageDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Finite weighted residual capture is monotone submodular with cover boundaries.",H("Weighted Residual Coverage"),Blocks(Describe.Lean(DescribeId.Create("weighted-gain-is-submodular"),DeclarationHandle.Create("D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage.weightedGain_submodular_insert"),H("Weighted gain has diminishing returns"),StatementSource.FromAuthor(Formula()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("WeightedGain and MarginalGain are finite sums over the fixed residual universe with its weight and separation predicate.")),Paragraph(Text("The insertion identity reduces the four-term inequality to marginalGain_antitone, so larger selected sets have no larger additional gain."))),DescribeRole.Theorem))));
 private static Formula Formula(){var r=F.Id("residuals");var w=F.Id("weight");var s=F.Id("separates");var sm=F.Id("smaller");var lg=F.Id("larger");var d=F.Id("definition");Formula g(Formula x)=>Call("WeightedGain",r,w,s,x);return Disp(Seq(OpenBracket,Call("DecidableEq",F.Id("Definition")),CloseBracket,Sp,Call("Subset",sm,lg),Sp,Rightarrow,g(Call("insert",d,lg)),Sp,Plus,Sp,g(sm),Sp,Leq,Sp,g(Call("insert",d,sm)),Sp,Plus,Sp,g(lg),Dot));}
}
