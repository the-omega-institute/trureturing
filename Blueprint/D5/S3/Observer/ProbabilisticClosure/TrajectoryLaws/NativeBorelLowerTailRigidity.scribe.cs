using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelLowerTailRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.";
    public DocumentDefinition Create()
    {
        Formula flow=F.Id("F"), remainder=F.Id("R"), q=F.Id("Q"), w=F.Id("W"), x=F.Id("x");
        Formula f=F.Id("f"), h=F.Id("h"), n=F.Id("n"), k=F.Id("k"), i=F.Id("i"), threshold=F.Id("N"), theta=F.Id("theta");
        Formula za=Fraction(D(2),D(9)), zb=Fraction(D(6),D(2,5));
        Formula p=Endpoint("p",true), beta=Endpoint("beta",true), mass=Mass(Field("nuP",flow),p);
        Formula lowerMean=Eqn(Mean(flow,Plus(n,D(3))),Multiply(Pow(za,D(3)),Mean(flow,n)));
        Formula iterator=Call("realIterate",flow,f,n,q);
        Formula subtractIterate=Eqn(Call("realIterate",flow,Call("subtractFunctions",f,h),n,q),
            Minus(iterator,Call("realIterate",flow,h,n,q)));
        Formula coordinateIterates=Eqn(RealCoordinate(Plus(k,n),i,q),
            Call("realIterate",flow,Call("realCoordinateFunction",k,i),n,q));
        Formula gapBound=And(Le(D(0),Call("lowerGap",q)),
            Le(Multiply(Pow(za,D(3)),Call("defect",F.Id("false"),q)),Call("lowerGap",q)));
        Formula gapIterates=Eqn(Call("realIterate",flow,F.Id("lowerGap"),n,q),
            Minus(RealCoordinate(Plus(n,D(3)),D(1),q),Multiply(Pow(za,D(3)),RealCoordinate(n,D(1),q))));
        Formula successors=And(
            AE(Field("nuP",flow),q,Implies(Eqn(q,p),AE(Call("B",flow,q),w,Eqn(w,beta)))),
            AE(Field("nuB",flow),w,Implies(Eqn(w,beta),AE(Call("A",flow,w),q,Eqn(q,p)))));
        Formula edges=And(Eqn(mass,Mass(Field("nuB",flow),beta)),And(
            AE(Field("GammaB",flow),x,Iff(Eqn(Call("fst",x),p),Eqn(Call("snd",x),beta))),
            AE(Field("GammaA",flow),x,Iff(Eqn(Call("fst",x),beta),Eqn(Call("snd",x),p)))));
        Formula excision=ExistsTyped(remainder,F.Id("CommonFlow"),And(
            Eqn(Field("nuP",remainder),Call("cond",Field("nuP",flow),Complement(Singleton(p)))),And(
            Eqn(Field("nuB",remainder),Call("cond",Field("nuB",flow),Complement(Singleton(beta)))),And(
            Eqn(Field("GammaB",remainder),Smul(Call("inverse",Minus(D(1),mass)),
                Call("restrict",Field("GammaB",flow),Complement(Call("preimage",F.Id("fst"),Singleton(p)))))),And(
            Eqn(Field("GammaA",remainder),Smul(Call("inverse",Minus(D(1),mass)),
                Call("restrict",Field("GammaA",flow),Complement(Call("preimage",F.Id("fst"),Singleton(beta)))))),And(
            Eqn(Field("B",remainder),Field("B",flow)),Eqn(Field("A",remainder),Field("A",flow))))))));
        Formula complement=ExistsTyped(remainder,F.Id("CommonFlow"),And(
            Eqn(Mass(Field("nuP",remainder),p),D(0)),FourDecompositions(flow,remainder,mass)));
        Formula recurrence=All(Implies(Le(threshold,n),Eqn(
            Plus(Minus(Mean(flow,Plus(n,D(2))),Multiply(Seq(Open,Plus(za,zb),Close),Mean(flow,Plus(n,D(1))))),
                Multiply(Multiply(za,zb),Mean(flow,n))),D(0))),("n",F.Id("Nat")));
        Formula endpointMixture=ExistsTyped(theta,F.Id("Real"),And(Le(D(0),theta),And(Le(theta,D(1)),
            FourNativeMixtures(flow,Call("ofReal",Minus(D(1),theta)),Call("ofReal",theta)))));
        return DocumentDefinition.Create(ScribeNode.Create("Borel endpoint recurrence and the original full flows",
            H("Exact recurrence rigidity on the full descriptor spaces"),Blocks(
                Paragraph(Text("F is the original boxed Borel CommonFlow. Its two marginals are probability measures on regular full legal-tail descriptors; GammaB and GammaA are its given directional joint measures, with their given conditional kernels B and A. Both normalized residual equations and both complete endpoint boxes are part of CommonFlow. The full legal carriers include the infinite noncompletion outcome. No atomicity, finite support, midpoint mean, loss budget or deterministic successor condition is added.")),
                Paragraph(Text("The lower native endpoint is a=1/3 and the upper endpoint is b=2/5. Their return rates are za=2/9 and zb=6/25; their marker-one coefficients are 4/9 and 9/25. nativeEndpoint(p,false) and nativeEndpoint(beta,false) are the lower full laws, and true selects the upper full laws. meanCoordinate(F,n) denotes the integral of the real marker-one coordinate at depth n against the original nuP. AE(mu,Q,P) means P holds mu-almost everywhere. cond(mu,S) is normalized restriction to S; mass(mu,x) evaluates the singleton {x}. All measure coefficients in the excision and decomposition formulas belong to ENNReal, and ofReal converts the final real weights.")),
                Node("iterate_sub",All(Implies(And(Call("Bounded",f),Call("Bounded",h)),AE(Field("nuP",flow),q,subtractIterate)),
                    ("F",F.Id("CommonFlow")),("f",Call("Map",F.Id("PDescriptor"),F.Id("Real"))),
                    ("h",Call("Map",F.Id("PDescriptor"),F.Id("Real"))),("n",F.Id("Nat"))),
                    "subtractFunctions(f,h)(Q)=f(Q)-h(Q). The bounded real return action preserves subtraction. Its almost-everywhere congruence propagates the identity through each finite iterate."),
                Node("coordinate_iterates",All(AE(Field("nuP",flow),q,coordinateIterates),
                    ("F",F.Id("CommonFlow")),("k",F.Id("Nat")),("n",F.Id("Nat")),("i",F.Id("Letter"))),
                    "realCoordinateFunction(k,i)(Q)=toReal(coordinate(k,i,Q)); realIterate(F,f,n,Q) evaluates the nth bounded real action iterate. The original full residual equations identify coordinate(k+n,i) with this iterate, for either letter."),
                Node("lowerGap",All(Eqn(Call("lowerGap",q),Minus(RealCoordinate(D(3),D(1),q),
                    Multiply(Pow(za,D(3)),Call("toReal",Call("g",q))))),("Q",F.Id("PDescriptor"))),
                    "The third-return lower gap compares the full depth-three marker-one mass with za cubed times the initial marker-one mass.",DescribeRole.Definition),
                Node("bounded_lowerGap",Call("Bounded",F.Id("lowerGap")),
                    "Each real coordinate is measurable and bounded between zero and one, so their indicated linear combination is a bounded measurable real function."),
                Node("lowerGap_bound",All(AE(Field("nuP",flow),q,gapBound),("F",F.Id("CommonFlow"))),
                    "The lower depth-three box gives L cubed g at least (4/9)za cubed. The original regular emission bound gives g at most 4/9. Thus the gap dominates za cubed times defect(false,Q)=4/9-toReal(g(Q)), which is nonnegative."),
                Node("lowerGap_iterates",All(AE(Field("nuP",flow),q,gapIterates),
                    ("F",F.Id("CommonFlow")),("n",F.Id("Nat"))),
                    "Subtraction, scalar multiplication and the full coordinate recursion express every iterate of the gap by the two original marker-one coordinates."),
                Node("lower_completion",All(Implies(lowerMean,AE(Field("nuP",flow),q,
                    Eqn(Call("toReal",Call("g",q)),Fraction(D(4),D(9))))),
                    ("F",F.Id("CommonFlow")),("n",F.Id("Nat"))),
                    "The mean equality makes the integral of L to the nth power of the gap zero. The integrated iterate bound is at least (1/5) to the nth power times the integral of the nonnegative gap. Hence the gap vanishes almost everywhere, and its positive multiple of the completion defect also vanishes. This identifies g=4/9 at the original marginal."),
                Node("lower_native_flow",All(Implies(lowerMean,FourPureNative(flow,false)),
                    ("F",F.Id("CommonFlow")),("n",F.Id("Nat"))),
                    "The completion identity makes the lower defect integral zero. The complete measurable-event total variation estimates force zero full-law loss in both phases. Directed event bounds and measure extensionality identify each entire descriptor, including infinity. The two actual joint measures then have both coordinates fixed by their original marginals, giving the two indicated unit flows."),
                Node("upper_native_successors",All(successors,("F",F.Id("CommonFlow"))),
                    "The upper endpoint limit and surviving-transition theorem identify the actual B successor of an upper native p descriptor. On an upper beta descriptor, the original A barycentre is the upper p law. The endpoint event is extremal in its full box, so its nonnegative complete-law loss has zero integral; almost every actual A successor is therefore the entire upper p descriptor."),
                Node("upper_native_edges",All(edges,("F",F.Id("CommonFlow"))),
                    "Outgoing absorption in the two directions yields opposite inequalities between the upper singleton masses. They are equal. The corresponding equal-mass event inclusions imply almost-everywhere equivalence of the two endpoint events in each actual directional joint, excluding all incoming and outgoing complement edges."),
                Node("upper_excision",All(Implies(Lt(mass,D(1)),excision),("F",F.Id("CommonFlow"))),
                    "Normalize the original marginal restrictions off the upper native singletons by the common positive mass 1-m. Restrict the actual joints by their first-coordinate complement and scale by the same reciprocal. The no-edge equivalences identify the second marginals. Absolute continuity preserves both complete boxes and normalized full residual equations. The resulting CommonFlow uses exactly the original B and A kernels on the same ambient spaces."),
                Node("upper_complement_decomposition",All(Implies(Lt(mass,D(1)),complement),("F",F.Id("CommonFlow"))),
                    "The same remainder has zero upper singleton mass. Splitting each original measure into its singleton part and complement gives all four exact decompositions with the same upper coefficient m. In each joint, the singleton event is the matching native endpoint pair."),
                Node("recurrence_native_flow",All(Implies(recurrence,endpointMixture),
                    ("F",F.Id("CommonFlow")),("N",F.Id("Nat"))),
                    "Let m be the original upper native singleton mass. If m=1, absorption exhausts both original marginals and joints. Otherwise the same-kernel complement has zero upper mass and inherits the exact recurrence after subtracting the upper geometric sequence. Its normalized mean d(n)/zb to the nth power tends to zero. The scaled first difference (d(n+1)-za*d(n))/zb to the nth power is constant on the recurrence tail and tends to zero, so the remainder obeys the lower three-return equality. Lower native completion identifies all four remainder measures. Restoring the two original upper unit subflows gives the displayed formulas with theta=toReal(m), including theta=0 and theta=1. The recurrence is an added exact eventual assumption; the conclusion determines all earlier complete words and the given full directional measures."))));
    }
    private static Formula FourPureNative(Formula flow,bool upper) => And(
        Eqn(Field("nuP",flow),Dirac(Endpoint("p",upper))),And(
        Eqn(Field("nuB",flow),Dirac(Endpoint("beta",upper))),And(
        Eqn(Field("GammaB",flow),Dirac(Pair(Endpoint("p",upper),Endpoint("beta",upper)))),
        Eqn(Field("GammaA",flow),Dirac(Pair(Endpoint("beta",upper),Endpoint("p",upper)))))));
    private static Formula FourNativeMixtures(Formula flow,Formula lower,Formula upper) => And(
        Eqn(Field("nuP",flow),Plus(Smul(lower,Dirac(Endpoint("p",false))),Smul(upper,Dirac(Endpoint("p",true))))),And(
        Eqn(Field("nuB",flow),Plus(Smul(lower,Dirac(Endpoint("beta",false))),Smul(upper,Dirac(Endpoint("beta",true))))),And(
        Eqn(Field("GammaB",flow),Plus(Smul(lower,Dirac(Pair(Endpoint("p",false),Endpoint("beta",false)))),Smul(upper,Dirac(Pair(Endpoint("p",true),Endpoint("beta",true)))))),
        Eqn(Field("GammaA",flow),Plus(Smul(lower,Dirac(Pair(Endpoint("beta",false),Endpoint("p",false)))),Smul(upper,Dirac(Pair(Endpoint("beta",true),Endpoint("p",true)))))))));
    private static Formula FourDecompositions(Formula flow,Formula remainder,Formula mass) => And(
        Decomposition("nuP",flow,remainder,mass,Endpoint("p",true)),And(
        Decomposition("nuB",flow,remainder,mass,Endpoint("beta",true)),And(
        Decomposition("GammaB",flow,remainder,mass,Pair(Endpoint("p",true),Endpoint("beta",true))),
        Decomposition("GammaA",flow,remainder,mass,Pair(Endpoint("beta",true),Endpoint("p",true))))));
    private static Formula Decomposition(string field,Formula flow,Formula remainder,Formula mass,Formula atom) =>
        Eqn(Field(field,flow),Plus(Smul(Minus(D(1),mass),Field(field,remainder)),Smul(mass,Dirac(atom))));
    private static DocumentBlock.Describe Node(string declaration,Formula formula,string prose,DescribeRole role=DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+declaration),
            H(declaration.Replace('_',' ')),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),role);
    private static Formula Field(string name,Formula flow) => Call(name,flow);
    private static Formula Endpoint(string phase,bool upper) => Call("nativeEndpoint",F.Id(phase),F.Id(upper ? "true" : "false"));
    private static Formula RealCoordinate(Formula n,Formula i,Formula q) => Call("toReal",Call("coordinate",n,i,q));
    private static Formula Mean(Formula flow,Formula n) => Call("meanCoordinate",flow,n);
    private static Formula Mass(Formula measure,Formula atom) => Call("mass",measure,atom);
    private static Formula Singleton(Formula atom) => Call("singleton",atom);
    private static Formula Complement(Formula set) => Call("complement",set);
    private static Formula Dirac(Formula atom) => Call("dirac",atom);
    private static Formula Pair(Formula a,Formula b) => Seq(Open,a,Comma,Sp,b,Close);
    private static Formula Smul(Formula a,Formula b) => Call("smul",a,b);
    private static Formula Fraction(Formula a,Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a,Formula b) => Seq(Grp(a),Caret,Grp(b));
    private static Formula Plus(Formula a,Formula b) => Seq(Grp(a),F.Plus,Grp(b));
    private static Formula Minus(Formula a,Formula b) => Seq(Grp(a),F.Minus,Grp(b));
    private static Formula Eqn(Formula a,Formula b) => Seq(a,Eq,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Leq,Sp,b);
    private static Formula Lt(Formula a,Formula b) => Seq(a,F.Lt,Sp,b);
    private static Formula And(Formula a,Formula b) => Seq(Open,a,Close,Land,Sp,Open,b,Close);
    private static Formula Implies(Formula a,Formula b) => Seq(Open,a,Close,Rightarrow,Sp,Open,b,Close);
    private static Formula Iff(Formula a,Formula b) => Seq(a,Leftrightarrow,Sp,b);
    private static Formula AE(Formula mu,Formula variable,Formula body) => Call("AE",mu,variable,body);
    private static Formula ExistsTyped(Formula variable,Formula type,Formula body) => Seq(Exists,Sp,variable,Colon,Sp,type,Comma,Sp,body);
    private static Formula All(Formula body,params (string Name,Formula Type)[] xs)
    {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,xs[k].Type,Comma,Sp,body);
        return body;
    }
}
