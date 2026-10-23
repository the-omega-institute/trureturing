using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativePaidHistoryCommonRowDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "Native paid-history law control", H("Native paid-history law control"), Blocks(
      Paragraph(Text("The original finite COMPLETE carrier, source-independent M.init and ordered acquired M.update are retained. Alpha is read 0 and beta is read 1. The literal suffix S=reads[1,0,1,1,0,0] accepts seed 1 and writes marker 100 before the held fourth latch. Every window and every appended return is an actual finite paid history; the average of their rows is never asserted to be a posterior row of one history.")),
      Node("native_paid_window_control","Literal native paid-window control","NativeWindowFacts","NativeWindowFacts denotes the full conjunction in the Lean telescope: render and reconstruct the actual operation list, exact alpha/beta counts, positive depth likelihoods and positive original normalizer, actual row support on the held active fibre, the copied original fullLaw identity through fullRenderer, configuration and law bounds with their distinct original phase suprema, equality of raw and installed law risk, the quadratic log-ratio envelope and strict native competing-depth entropy. The original all-PhaseHistory suprema include every rejection and return.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("e","InstalledEmitterM"), ("mu","PMFDepth"), ("m","Natural"), ("t","Natural"), ("j","Natural"), ("s","ActivePhase")),
      Node("native_growing_window_likelihood","Quadratic control on growing windows","GrowingWindowLikelihood","For w>=2 and u,v<w, set N=w^3, m=floor(N*r_k)+u and t=floor(N*(1-r_k))+v. GrowingWindowLikelihood is log(L_i/L_k)<=18/w+suffixLogRatio(j,s,k,i). The proof uses r_k(1-r_k)>=2/9 and the quadratic empirical Bernoulli log inequality. The fixed latch and return likelihood factors are retained. This is a uniform upper envelope, not a uniform positive depth gap.", ("k","Depth"), ("i","Depth"), ("w","Natural"), ("u","Natural"), ("v","Natural"), ("j","Natural"), ("s","ActivePhase")),
      Node("native_countable_posterior_concentration","Uniform posterior collapse for each supported depth","UniformPosteriorCollapse","UniformPosteriorCollapse means: for each epsilon>0, eventually w>=2 and for every u,v<w the original posterior of the actual window at k has 1-posterior(k).toReal<epsilon. The prior is one arbitrary PMF on positive integers, including countable accumulating native rates. Strict native KL gives each fixed competitor cubic decay; the min of that decay and exp(16+2*j) dominates every finite-window competitor. Original prior weights supply a summable envelope, and pinned Tannery dominated convergence closes the countable sum. Fixed return words do not change the prior or conditioning.", ("mu","PMFDepth"), ("k","SupportedDepthMu"), ("j","Natural"), ("s","ActivePhase")),
      Node("native_countable_target_concentration","Complete countable target convergence in total variation","UniformCompleteTargetTV","UniformCompleteTargetTV has the same epsilon, eventual-window and all-offset quantifiers as posterior collapse. Its error is measurableTotalVariation(rawTarget(mu,H),pureTail(k,s)).toReal. pureTail is the original rawReadLaw(r_k) mapped by validStopped, including the noncompletion outcome. The original conditional target is the countable posterior mixture of these complete laws; its total variation from the supported atom law is at most 1-posterior(k). No finite TV vector substitutes for this countable law.", ("mu","PMFDepth"), ("k","SupportedDepthMu"), ("j","Natural"), ("s","ActivePhase")),
      Node("installed_law_invariant","Invariant generator agreement preserves the entire infinite law","InstalledLawInvariant","InstalledLawInvariant assumes the same projected native fields, equality of the marked acquired generators on G and closure of their original positive supports. It proves equality of markedLaw on the entire infinite path space, then of fullLaw and every tailLaw. Prefix coupling gives equality and support propagation at each finite cut. The original path_ext supplier applies projective uniqueness to extend those equalities to all measurable infinite events. This preserves noncompletion, rather than inferring almost-sure completion from finite-word recursion.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("N","ObserverZ"), ("e","InstalledEmitterM"), ("f","InstalledEmitterN"), ("G","InvariantConfigurations"), ("z","ConfigurationInG")))));
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
