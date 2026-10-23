using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelSuperharmonicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.";
    public DocumentDefinition Create()
    {
        Formula flow=F.Id("F"), q=F.Id("Q"), r=F.Id("R");
        Formula mu=Call("nuP",flow), hv=Call("h",flow,q), ev=Call("excess",q);
        Formula hh=Call("threeStepAverage",flow,q), delta=Call("delta",flow,q);
        Formula th=Call("normalizedAction",flow,Call("threeStepAverage",flow),q);
        Formula lim=Call("q",flow,q), seq=Call("qIterateAt",flow,q);
        Formula fv=Call("sixthFunctional",flow,q);
        Formula tf=Call("normalizedAction",flow,Call("sixthFunctional",flow),q);
        Formula cf=Call("lintegral",Call("CRow",flow,q),r,Call("sixthFunctional",flow,r));
        Formula signed=All(And(
            Call("Measurable",Call("descriptorTVBorel",F.Id("p")),F.Id("BorelR"),Call("h",flow)),
            Ae(mu,q,And(Le(Fraction(D(3),D(2,5)),hv),Le(hv,Fraction(D(1),D(2))),Le(D(0),ev),
                Eqn(delta,Fraction(Sub(Call("toReal",Call("g",q)),
                    Call("toReal",Call("normalizedIterate",flow,F.Id("g"),D(3),q))),D(3))),
                Le(Fraction(ev,D(3)),delta),Le(th,hh)))),("F","CommonFlow"));
        Formula limit=All(And(Call("Measurable",Call("q",flow)),Ae(mu,q,And(
            Call("Antitone",seq),Call("Tendsto",seq,F.Id("atTop"),Call("Nhds",lim)),
            Le(lim,hh),Eqn(Call("normalizedAction",flow,Call("q",flow),q),lim)))),("F","CommonFlow"));
        Formula gain=All(Ae(mu,q,Le(Mul(fv,Call("ofReal",Add(D(1),Fraction(Mul(D(1,0),ev),D(3))))),tf)),("F","CommonFlow"));
        Formula domination=Le(Call("smul",Call("inv",F.Id("endpointRate")),Call("LRow",flow,q)),
            Call("smul",Call("ofReal",Add(D(1),Fraction(Mul(D(2,5),ev),D(9)))),Call("CRow",flow,q)));
        Formula unweighted=All(Ae(mu,q,And(domination,
            Le(Add(fv,Mul(Mul(Fraction(D(9),D(2,0)),Call("ofReal",ev)),fv)),cf))), ("F","CommonFlow"));
        return DocumentDefinition.Create(ScribeNode.Create("Superharmonic completion on the acquired chain", H("Signed defect, harmonic limit and sixth-power gain"), Blocks(
            Paragraph(Text("F is an arbitrary original boxed CommonFlow. The acquired return chain is C=BA with its original stationary unweighted p marginal, and L has the original (1-u)*v weights. T is normalizedAction, with endpointRate=6/25. The ENNReal threeStepAverage is (g+Tg+T squared g)/3; h is its real value, excess=g.toReal-9/25, and delta=h-(Th).toReal uses signed real subtraction. AE(mu,Q,P) means P holds for mu-almost every Q. qIterateAt(F,Q) denotes the sequence n mapped to qIterate(F,n,Q). CRow and LRow denote the actual acquired rows.")),
            Node("h_finite",All(Seq(hh,Neq,Sp,F.Id("top")),("F","CommonFlow"),("Q","PDescriptor")),"All original normalized g iterates are finite, using L <= C and finite endpointRate inverse. Their finite three-step sum is finite. This bound is consumed by Holder, real conversion and stationary cancellation."),
            Node("h_global_bound",All(Le(hh,D(1,0)),("F","CommonFlow"),("Q","PDescriptor")),"The global g bound one and normalized iterate bounds (25/6) to the powers one and two bound the finite three-step average by ten. This global bound is consumed by row integrability and stationary localization."),
            Node("sixth_le_h",All(Le(fv,hh),("F","CommonFlow"),("Q","PDescriptor")),"q is bounded above by the first term of its infimum, namely threeStepAverage. If h is zero, q is zero. Otherwise cancellation gives q to the sixth power divided by h to the fifth power <= h. This bound supplies finite sixth-functional integrals."),
            Node("sixth_measurable",All(Call("Measurable",Call("sixthFunctional",flow)),("F","CommonFlow")),"Countable-infimum measurability and measurable finite powers and division give measurability of the actual sixth functional. This is consumed by Holder and the stationary integral identity."),
            Node("common_flow_signed_h",signed,"h is measurable for the actual TV-Borel sigma algebra on the exact p descriptor. The original three-step upper endpoint box supplies the signed defect. Finite row domination makes every normalized g iterate finite, so conversion to real values preserves the signed identity. The bound h <= 1/2 follows from g <= 4/9 and T <= (10/9) C for the first two iterates. A global bound ten ensures finite row integrals."),
            Node("common_flow_q_limit",limit,"qIterate(F,n) is T to the power n applied to the same threeStepAverage, and q is its infimum over all natural n. The initial decrease follows from the signed defect. Stationarity of C transports subsequent conull inequalities to acquired rows, and L <= C transfers them to weighted rows. Decreasing monotone convergence applies because the first row integral is finite. Dropping the first term leaves the infimum unchanged."),
            Node("common_flow_sixth_power_gain",gain,"sixthFunctional is q to the sixth power divided by threeStepAverage to the fifth power, on the same actual flow. Weighted Holder with exponents 1/6 and 5/6, followed by Tq=q, gives q to the sixth power <= TF times (Th) to the fifth power. The signed defect and h <= 1/2 yield the displayed multiplicative gain. Positive h and finite row bounds justify division and conversion to reals."),
            Node("common_flow_unweighted_gain",unweighted,"The full B completion equation gives g >= (1-u)*(3/5), while v <= 2/5 bounds the actual weighted row. Thus T <= (1+25*excess/9) C on the original marginal. Together with the sixth-power gain and 0 <= excess <= 19/225, this gives CF >= F+(9/20)*excess*F. The two inequalities use the same acquired B and A, and the margin remains unweighted."))));
    }
    private static DocumentBlock.Describe Node(string declaration, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(Prefix+declaration),
        H(declaration.Replace('_',' ')), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a,Eq,b);
    private static Formula Add(Formula a, Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open,a,Minus,b,Close);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula And(params Formula[] xs) {
        Formula body=xs[0];
        for(int k=1;k<xs.Length;k++) body=Seq(body,Sp,Land,Sp,xs[k]);
        return Seq(Open,body,Close);
    }
    private static Formula Ae(Formula mu, Formula x, Formula body) => Call("AE",mu,x,body);
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
}
