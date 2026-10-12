using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativePaidHistoryCommonRowLimitsDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "Attainable stationary supports and law-preserving restriction", H("Attainable stationary supports and law-preserving restriction"), Blocks(
      Paragraph(Text("Every matrix entry is M.update(op,x)(y).toReal. Ralpha and Rbeta are the ordered actual equal-pair products; the latch is the exact six-letter product. Return is the acquired beta-alpha product BA. Emissions do not weight these kernels.")),
      Node("native_common_window_limit","Common stochastic Cesaro limits and a rate-independent row","CommonWindowLimit","CommonWindowLimit gives stochastic E,F, one strictly increasing subsequence phi, and eta=M.init.toReal*(E*F*P_S). Both equal-pair kernels fix their respective limit on the left and right. Eta is nonnegative and sums to one. For every native depth k, the literal finite double average windowAverage(M,phi(n)+1,k) tends to this same eta; every positive coordinate has an actual finite window witness. Pinned IsCompact.tendsto_subseq chooses one matrix pair. Telescoping and left stochastic contraction justify arbitrary shifts, including periodic and reducible kernels; no full mean-ergodic projection is assumed.", ("Z","FiniteType"), ("M","ObserverZ")),
      Node("native_common_stationary_rows","Common reachable stationary rows with constraint transport","CommonStationaryRows","CommonStationaryRows gives pi,tau,eta and the same common window subsequence before every depth quantifier. The rows are nonnegative and normalized, pi*BA=pi, pi*B=tau and tau*A=pi. Positive pi and tau labels have actual finite window-with-return witnesses. Positive B/A flows remain in the opposite positive support. A second common Cesaro cluster of BA also preserves every closed convex pair of phase constraints already satisfied by all finite-return orbits of eta. Applying this transport to the native risk region preserves every phase bound simultaneously. The bind_real identity and returned_average_actual connect real matrix products with actual PMF rows.", ("Z","FiniteType"), ("M","ObserverZ")),
      Node("native_support_clipping","Zero-label deletion preserves the original complete laws","NativeSupportClipping","NativeSupportClipping assumes hX and hY place every positive pi and tau label on its original held phase fibre. Both hB and hA require the actual acquired read-1 and read-0 supports to lie in the opposite support. Under these hypotheses it constructs a retraction q that is the identity on retained labels and preserves project. Only zero stationary labels at the designated held active fibre are removed from transition columns; original pending, delivered and other native fields are retained. clippedObserver keeps M.init and maps acquired successors through q; clippedEmitter keeps the exact original e.emit. On positive pi and tau labels the original B and A rows are unchanged. All clipped transition support lies in retained labels. From each positive label, the clipped and original marked infinite trajectory laws, full laws and tail laws are equal. Endpoint completion updates, pending Stop, original delivery blocks and noncompletion mass are retained.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("e","InstalledEmitterM"), ("pi","HeldPhasePRow"), ("tau","HeldPhaseBetaRow"), ("hX","PiHeldPhasePFibre"), ("hY","TauHeldPhaseBetaFibre"), ("hB","ActualReadOneSupportClosure"), ("hA","ActualReadZeroSupportClosure")))));
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
