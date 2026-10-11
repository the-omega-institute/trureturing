using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeEmissionClippingDocument : IScribeDocumentDefinition
{
  private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.";
  public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
    "NativeEmissionClipping", H("Lawful emission clipping on the original observer"), Blocks(
      Node("finite_event_clipping_budget","A finite disjoint-event clipping estimate","FiniteEventClippingBudget","P, R and T are probability measures on the same measurable carrier A. E and G are measurable and disjoint. The real masses of G under P and R are a and b with a less than or equal to b, and P(E)-R(E)=gap. Then the absolute difference between T(G) and max(a,min(b,T(G))) is at most TV(T,P).toReal plus TV(T,R).toReal minus gap. Testing E and E union G in the two possible orders detects deviations below a and above b. Testing E in both laws covers the intervening interval. TV uses the supremum over measurable events.", ("A","MeasurableType"), ("P","ProbabilityMeasureA"), ("R","ProbabilityMeasureA"), ("T","ProbabilityMeasureA"), ("E","MeasurableSetA"), ("G","MeasurableSetA"), ("hd","DisjointEG"), ("a","Real"), ("b","Real"), ("gap","Real"), ("hab","OrderedEndpoints"), ("ha","PMassGa"), ("hb","RMassGb"), ("he","EndpointEventGap")),
      Node("native_configuration_clipping_budget","Original configuration budgets for a lawful emission clamp","NativeConfigurationClippingBudget","The comparison emitter keeps the original finite carrier and every M.init and M.update kernel. It clamps the real read0 probability into [1/3,2/5] only at fourth(active s), gives the other read its complement, and retains the original emitter at all other controls. It is an analytic probability comparison and asserts no executable exact-real sampler or fixed-resource preservation. At every original p configuration with the correct active control, the read0 change is bounded by the sum of its complete raw-law TVs to the depth-one and depth-two endpoint p laws minus twice 1116529/22781250. At every original beta configuration the corresponding bound subtracts twice 239/6750. The immediate completion masses are u and 1-v. The p witness is disjoint from some[0]; the complement of the beta witness is disjoint from some[1]. The original endpoint event evaluations supply the gaps. These are configuration bounds before averaging. They do not by themselves bound the comparison emitter worst-history risk or establish the strict original-observer gap.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("e","InstalledEmitterM")),
      Node("clamp_box","Clamped emissions stay in the comparison interval","ClampBox","For every real t, max(1/3,min(2/5,t)) lies in [1/3,2/5].", ("t","Real")),
      Node("clamp_read_zero","The comparison next-read probability","ClampReadZero","For every finite measurable singleton carrier Z, Observer M, lawful emitter e, configuration z and active phase s whose actual projected control is fourth(active s), the real read0 probability of clampedEmitter M e at z equals clampEmission of the original real read0 probability. Other controls retain e.", ("Z","FiniteMeasurableSingletonType"), ("M","ObserverZ"), ("e","InstalledEmitterM"), ("z","Z"), ("s","ActivePhase"), ("hz","ActualActiveControl")))));
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
