using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class CompleteTailGeometricSurvivalDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "CompleteTailGeometricSurvival", H("Complete-event geometric survival"), Blocks(
      Node("regular_complete_survival","Two-read survival and noncompletion","RegularCompleteSurvival","For any finite types X and Y and actual RegularTable R, survivalEvent(n) contains none and finite words longer than n. At every x and y, its complete-law mass at cut 2n is at most (4/15)^n. The prefix inverse identity holds also for none. Two real all-event recursions multiply the upper continuation coefficients 2/3 and 2/5; row normalization gives a uniform two-read bound. The geometric bound tends to zero, hence each Q(x) and W(y) assigns zero mass to none. No properness assumption is required in addition to the RegularTable generation fields. This applies to the clamped native comparison, while the original emitter may retain noncompletion mass.", ("X","FiniteType"), ("Y","FiniteType"), ("R","RegularTableXY")))));

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
