using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelCEventDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.";
    public DocumentDefinition Create()
    {
        Formula f=F.Id("F"), q=F.Id("Q"), r=F.Id("R"), x=F.Id("x"), n=F.Id("n");
        Formula p=Call("originalTrajectory",f), nu=Call("nuP",f), ev=Call("summableExcess");
        Formula fq=Call("eventProbability",f,q), fr=Call("eventProbability",f,r);
        Formula harm=All(And(Eqn(Call("map",p,Call("shift")),p),
            And(Eqn(Call("preimage",Call("shift"),ev),ev),
                All(Eqn(Call("lintegral",Call("CRow",f,q),r,fr),fq),("Q","PDescriptor")))),
            ("F","CommonFlow"));
        Formula local=All(Call("AE",nu,q,And(Eqn(Multiply(Call("ofReal",Call("excess",q)),fq),D(0)),
            Imp(Seq(fq,Neq,Sp,D(0)),Eqn(Call("excess",q),D(0))))),("F","CommonFlow"));
        Formula edges=All(Call("AE",nu,q,Call("AE",Call("CRow",f,q),r,Eqn(fr,fq))),
            ("F","CommonFlow"));
        Formula carrier=And(All(Le(D(0),Call("excess",Call("at",x,n))),("n","Nat")),
            Iffn(Call("member",x,ev),Call("Summable",n,Call("excess",Call("at",x,n)))));
        Formula real=All(And(Call("AE",p,x,carrier),
            Call("AE",nu,q,Call("AE",Call("startedCRow",f,q),x,carrier))),
            ("F","CommonFlow"));
        Formula cond=All(Call("AE",nu,q,Eqn(Call("conditionalRow",p,Call("identity"),Call("evalZero"),q),
            Call("startedCRow",f,q))),("F","CommonFlow"));
        return DocumentDefinition.Create(ScribeNode.Create("The original summable-excess event",
            H("Started trajectories and stationarity"),Blocks(
                Paragraph(Text("startedC(F,Q) is the Ionescu-Tulcea kernel for the original C=BA with its initial descriptor fixed to Q. originalTrajectory(F) is its mixture against the original stationary margin nuP. shift(x)(n)=x(n+1). excessSeries(x) is the extended nonnegative sum of ofReal(excess(x(n))); summableExcess is the measurable event excessSeries<infinity. eventProbability(F,Q)=startedC(F,Q)(summableExcess). Every series uses the actual successive states of this C law.")),
                Describe.Lean(DescribeId.Create("measure-eq-of-prefix"),
                    DeclarationHandle.Create(Prefix+"measure_eq_of_prefix"),
                    H("Prefix marginals determine a complete sequence measure"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For any measurable alphabet S and measures mu and nu on natural sequences, assume nu is finite and every prefix of length n+1 has the same pushforward measure under mu and nu. Then mu equals nu on the entire product sigma-algebra. Every finite coordinate set lies in one prefix; Mathlib IsProjectiveLimit.unique applies to the finite-coordinate marginals of nu. This determines the native started trajectory laws and the complete conditional future and past measures of OriginalFutureScreening."))), DescribeRole.Theorem),
                Node("common_flow_event_harmonic",harm,"The finite C products commute with deletion of their first coordinate. Uniqueness of the full law from its finite marginals gives the actual started-row shift identity and then stationarity of the original path law. Removing one finite term preserves the finite-series event. Evaluating this identity at that event proves harmonicity of its actual probability for every starting descriptor."),
                Node("common_flow_event_localization",local,"The bounded measurable reciprocal (1+excessSeries)^(-1) increases under shift and has the same integral by stationarity. It therefore agrees almost everywhere with its shifted value. On the finite-series event, finite cancellation forces the initial excess to vanish. Disintegrating against the actual started rows gives ofReal(excess(Q))*eventProbability(F,Q)=0. The earned nonnegative excess on the original margin then gives the real zero-excess implication, including the case of event probability zero."),
                Node("common_flow_event_edges",edges,"The harmonic event probability lies in [0,1]. The stationary second moment and the conditional square inequality force zero conditional variance. Thus the probability has the same value at both states of almost every original C edge. This statement concerns the actual event probability."),
                Paragraph(Math(real), Text("Every time marginal of the same original path law is nuP. The source excess bound therefore holds simultaneously at all countably many times. On this carrier the nonnegative extended series is finite exactly when the original real excess series is summable. The same assertion holds in almost every started row after disintegration against nuP.")),
                Node("common_flow_event_conditional",cond,"conditionalRow(P,identity,evalZero,Q) is the regular conditional distribution of the entire path given its time-zero descriptor. Each started row has that descriptor as its initial state. This proves the full joint identity and identifies the exhibited started kernel with the conditional law almost everywhere. Standard-Borel structure is used for this actual conditional distribution."))));
    }
    private static DocumentBlock.Describe Node(string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+declaration), H(declaration.Replace('_',' ')),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Eqn(Formula a, Formula b) => Seq(a,Eq,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,b);
    private static Formula And(Formula a, Formula b) => Seq(a,Land,Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Close,Rightarrow,Open,b,Close);
    private static Formula Iffn(Formula a, Formula b) => Seq(Open,a,Close,Leftrightarrow,Open,b,Close);
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
}
