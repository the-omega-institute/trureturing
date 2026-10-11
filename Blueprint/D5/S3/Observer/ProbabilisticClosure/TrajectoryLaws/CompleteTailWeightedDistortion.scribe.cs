using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class CompleteTailWeightedDistortionDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "CompleteTailWeightedDistortion", H("Stationary weighted complete-law distortion"), Blocks(
      Node("stationary_weighted_complete_distortion","Distortion with primed continuation coefficients","StationaryWeightedCompleteDistortion","X and Y are arbitrary finite types. R is a RegularTable on X and Y, with normalized nonnegative rows, common stationarity, clamped u and v in [1/3,2/5], probability complete laws Qprime and Wprime, and their all-event generation equations. u and v are arbitrary real functions. Q and W are probability laws and satisfy the stated original all-event generation equations with the same B and A. For du=sum pi abs(u-uprime), dv=sum tau abs(v-vprime), DQ=sum pi TV(Q,Qprime).toReal and DW=sum tau TV(W,Wprime).toReal, DQ is at most du+(2/3)DW and DW is at most dv+(2/5)DQ. Thus DQ is at most (15du+10dv)/11 and DW is at most (6du+15dv)/11. The event supremum is taken at each configuration before the stationary average. The identity (u-uprime)(indicator-originalContinuation)+(1-uprime)(originalContinuation-primedContinuation) uses the primed continuation coefficient. The complete event domain includes the noncompletion atom. The original generator needs no contraction, properness or absolute continuity.", ("X","FiniteType"), ("Y","FiniteType"), ("R","RegularTableXY"), ("u","XToReal"), ("v","YToReal"), ("Q","XToProbabilityRawLaw"), ("W","YToProbabilityRawLaw"), ("hq","OriginalPGeneration"), ("hw","OriginalBetaGeneration")))));
  private static DocumentBlock.Describe Node(string name, string title, string predicate,
    string prose, params (string Name, string Type)[] parameters)
  {
    Formula statement = F.Seq(Operatorname, Grp(F.Id(predicate)), Open);
    for (int i=0; i<parameters.Length; i++)
      statement = i==0 ? F.Seq(statement,F.Id(parameters[i].Name)) :
        F.Seq(statement,Comma,Sp,F.Id(parameters[i].Name));
    statement = F.Seq(statement,Close);
    for (int i=parameters.Length-1; i>=0; i--)
      statement = F.Seq(Forall,Sp,F.Id(parameters[i].Name),Colon,F.Id(parameters[i].Type),
        Comma,Sp,Open,statement,Close);
    return Describe.Lean(DescribeId.Create(name.Replace('_','-')),
      DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(statement)),
      AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
  }
}
