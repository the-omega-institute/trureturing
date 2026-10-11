using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeStoppedTailRegenerationDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "NativeStoppedTailRegeneration", H("Complete native stopped laws"), Blocks(
      Node("stopped_read_cons","First completion under one prefixed read","StoppedReadCons","The stream is an arbitrary infinite binary stream. At p a leading zero completes with word [0], and at beta a leading one completes with word [1]. A leading one at p prefixes one to the beta stopped tail, while a leading zero at beta prefixes zero to the p stopped tail. Option.map sends none to none. The finite-word fibre theorem and the native parser establish both finite stopping shifts; exhaustiveness of Option then retains the infinite noncompletion case.", ("omega","BinaryStream")),
      Node("native_stopped_tail_regeneration","Complete native two-phase generation","NativeStoppedTailRegeneration","Z is the original finite COMPLETE carrier with its measurable singleton structure, M is the source-independent original observer and e is any lawful installed emitter. rawTailLaw is tailLaw pushed through Subtype.val, and remains a probability law. For each z whose projected control is fourth(active p), and every set E of raw tails, Q(z,E) equals u(z) times the indicator of some[0] in E plus (1-u(z)) times the sum over zprime of M.update(read1,z,zprime).toReal times W(zprime,prefix1 inverse E). For fourth(active beta) the corresponding equation is (1-v(z)) times the indicator of some[1] in E plus v(z) times the sum of M.update(read0,z,zprime).toReal times Q(zprime,prefix0 inverse E). Both u and v are the original read0 emission probability at the respective configuration. Each equation requires the actual current-control hypothesis; normalization alone does not provide it. The marked regeneration identity, incoming-mark invariance and almost-sure initial-head identity establish the pushforward law. All events, including none, are retained. Completing reads keep the matching pending Stop and its original update and full renderer.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("e","InstalledEmitterM")),
      Node("raw_projection_tv","Raw projection preserves total variation","RawProjectionTV","For every active phase s and arbitrary measures P and Q on ValidTail s, total variation of their Subtype.val pushforwards equals total variation of P and Q. The measurable retraction sends invalid words to valid none and is a left inverse on every valid tail. Probability or original termination is not required.", ("s","ActivePhase"), ("P","MeasureValidTailS"), ("Q","MeasureValidTailS")),
      Node("pure_raw_law","The endpoint source laws on raw tails","PureRawLaw","For every positive depth k and active phase s, pureTail(k,s) pushed through Subtype.val equals explicitStoppedWordLaw(s,rate(k)). This is a direct application of the original stopped-word pushforward theorem. In particular depths one and two have rates 1/3 and 2/5.", ("k","PositiveDepth"), ("s","ActivePhase")))));
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
