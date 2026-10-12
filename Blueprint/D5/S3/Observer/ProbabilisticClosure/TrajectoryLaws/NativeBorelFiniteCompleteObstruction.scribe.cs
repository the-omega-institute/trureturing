using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelFiniteCompleteObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.";
    public DocumentDefinition Create()
    {
        Formula z=F.Id("Z"), m=F.Id("M"), e=F.Id("e"), rho=F.Id("rho"), n=F.Id("n"), offset=F.Id("N");
        Formula p=F.Id("p"), x=F.Id("x"), op=F.Id("T"), l=F.Id("ell");
        Formula noRecurrence=All(Seq(Call("nonzero",p),Rightarrow,
            Seq(Exists,Sp,n,Colon,F.Id("Nat"),Comma,Sp,
                Call("nonzero",Call("recurrenceSum",p,offset,n)))),("p","RealPolynomial"),("N","Nat"));
        Formula linear=All(Call("Not",All(Seq(Call("averagedCompletion",Add(offset,n)),Eq,
            Call("apply",l,Call("apply",Call("pow",op,n),x))),("n","Nat"))),
            ("V","FiniteRealModule"),("T","EndV"),("x","V"),("ell","RealLinearFunctionalV"),("N","Nat"));
        Formula equation=Seq(Call("averagedCompletion",Add(offset,n)),Eq,
            Call("sumConfigurations",rho,Call("tailLaw",m,e,F.Id("p")),Call("pAtom",n,D(1))));
        Formula statement=All(Call("Not",All(equation,("n","Nat"))),
            ("Z","FiniteCompleteCarrier"),("M","ObserverZ"),("e","InstalledEmitterM"),("rho","PMFZ"),("N","Nat"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Excluding every original finite COMPLETE realization",
            H("Finite installed laws and the continuous boundary"),Blocks(
            new DocumentBlock.Section(H("The continuous endpoint-box common flow"), ContinuousBlocks()),
                Paragraph(Text("NativeFiniteWordCoordinates owns the periodic curve parameters and the installed cylinder-transfer suppliers. Their original declaration namespace is retained. The full continuous descriptors, common flow, moment obstruction and finite COMPLETE conclusion are owned here.")),
                Paragraph(Text("Z is any finite original COMPLETE carrier with its measurable space and measurable singletons. M is its original Observer with source-independent initialization and acquired-operation update rows. e is any lawful InstalledEmitter(M), with arbitrary real probability tables. rho is any starting configuration PMF on this same Z. sumConfigurations is sum over z of rho(z).toReal times the real singleton mass of the actual tailLaw(M,e,p,z). It therefore includes arbitrary original acquired starting distributions.")),
                Paragraph(Text("All moments are the original averagedCompletion(n), the integral of g(x)x^n against curveUniform on [239/1000,6/25). For a real polynomial p, recurrenceSum(p,N,n) is the sum over i in p.support of p.coeff(i) averagedCompletion(N+n+i). Every finite order and every finite initial offset N is included.")),
                Node("continuous-no-recurrence","continuous_no_linear_recurrence","No nonzero recurrence",noRecurrence,
                    "For nonzero p, its real roots form a finite set. The continuous parameter measure assigns that set zero mass, while g(x)x^N is strictly positive. Thus the integral of g(x)x^N p(x)^2 is strictly positive. Expanding one polynomial factor gives the finite weighted sum of polynomial moments. If every recurrenceSum vanished, expanding the other factor would make the same positive integral zero. The same continuous measure supplies every moment."),
                Node("continuous-no-finite-linear","continuous_no_finite_linear_realization","No finite-dimensional homogeneous linear realization",linear,
                    "FiniteRealModule is any real module with AddCommGroup and Module.Finite. T is any linear endomorphism, x any vector and ell any real linear functional. LinearMap.exists_monic_and_aeval_eq_zero supplies a nonzero monic annihilator for T. Applying ell to its action on T^n x gives exactly a finite recurrence. The continuous-moment result excludes equality of the entire sequence, after every finite initial offset. This consumed helper supplies the obstruction for the original installed laws below."),
                Describe.Lean(DescribeId.Create("continuous-no-finite-complete"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_finite_complete"),
                    H("No finite COMPLETE observer realizes even the averaged marker-one sequence"),
                    StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Use the actual marked-law regeneration equation on Marked(Z)=Z times Option(Operation). Mask each transition by the letter read from its incoming mark, exactly as rawFrom does. The two masks for beta then alpha give a homogeneous real linear endomorphism on the finite vector space of functions on Marked(Z). The complete word pWord(n,1) is n repetitions of [1,0] followed by [1,1]. Its exact stopped-word fiber is the corresponding prefix cylinder, so its actual tail singleton mass is the n-th power of that endomorphism applied to the final [1,1] cylinder vector. The original rho gives a linear readout at (z,none). This earns the finite-dimensional realization equation from the installed laws themselves. The continuous moment obstruction then excludes it for every finite carrier, every lawful emission table, every acquired update table and every rho, already at one mandatory full-law coordinate. Every finite offset N is also excluded.")),
                        Paragraph(Text("The strictly negative two-endpoint recurrence is one diagnostic of this same continuous law. Exclusion of arbitrary finite COMPLETE carriers uses the stronger obstruction to every finite-order recurrence and the actual installed-law transfer equation. The finite matrices here describe the existing complete carrier mathematically; no analysis coordinate is installed as a new observer register."))),DescribeRole.Theorem))));
    }
    private static BlockSequence ContinuousBlocks()
    {
        Formula t = F.Id("t"), n = F.Id("n"), k = F.Id("k"), s = F.Id("s");
        Formula q = F.Id("Q"), w = F.Id("W"), z = F.Id("Z"), x = F.Id("x");
        Formula descriptor = Call("curveDescriptor", s, t);
        Formula p = F.Id("p"), beta = F.Id("beta"), bit = F.Id("i");
        Formula pLaw = Call("law", Call("curveDescriptor", p, t));
        Formula bLaw = Call("law", Call("curveDescriptor", beta, t));
        Formula marker = Call("if", Eqn(bit,D(0)), Call("curveU",t), Call("curveG",t));
        Formula atomsP = AllCurve(Eqn(Call("realMass",pLaw,Call("pAtom",n,bit)),
            Mul(marker,Call("pow",t,n))), ("n","Nat"),("i","Letter"));
        Formula atomsB = AllCurve(Eqn(Call("realMass",bLaw,Call("betaAtom",n,bit)),
            Mul(Call("curveV",t),Mul(marker,Call("pow",t,n)))), ("n","Nat"),("i","Letter"));
        Formula complete = AllCurve(And(
            Eqn(Call("mass",Call("law",descriptor),F.Id("univ")),D(1)),
            Eqn(Call("mass",Call("law",descriptor),Call("infinity",s)),D(0)),
            Eqn(Call("mass",Call("law",descriptor),Call("tailSet",s,D(0))),
                Call("if",Eqn(s,p),D(1),Call("ofReal",Call("curveV",t)))),
            Call("EndpointBox",descriptor)), ("s","ActivePhase"));
        Formula family = And(AllCurve(Call("Measurable",Call("curveDescriptor",s)),("s","ActivePhase")),
            AllCurve(And(atomsP,atomsB,complete,
                Eqn(Call("residualB",Call("curveDescriptor",p,t)),bLaw),
                Eqn(Call("residualA",Call("curveDescriptor",beta,t)),pLaw)),("t","CurveParameter")));
        Formula sameX = And(
            Eqn(Call("B", F.Id("continuousCommonFlow"), Call("curveDescriptor", F.Id("p"), x)),
                Call("dirac", Call("curveDescriptor", F.Id("beta"), x))),
            Eqn(Call("A", F.Id("continuousCommonFlow"), Call("curveDescriptor", F.Id("beta"), x)),
                Call("dirac", Call("curveDescriptor", F.Id("p"), x))),
            Eqn(Call("C", F.Id("continuousCommonFlow"), Call("curveDescriptor", F.Id("p"), x)),
                Call("dirac", Call("curveDescriptor", F.Id("p"), x))));
        Formula graph = And(
            AllCurve(Eqn(Call("singletonMass", Call("nuP", F.Id("continuousCommonFlow")), q),D(0)), ("Q", "PDescriptor")),
            AllCurve(Eqn(Call("singletonMass", Call("nuB", F.Id("continuousCommonFlow")), w),D(0)), ("W", "BDescriptor")),
            AllCurve(Eqn(Call("singletonMass", Call("GammaB", F.Id("continuousCommonFlow")), z),D(0)), ("Z", "PDescriptorTimesBDescriptor")),
            AllCurve(Eqn(Call("singletonMass", Call("GammaA", F.Id("continuousCommonFlow")), z),D(0)), ("Z", "BDescriptorTimesPDescriptor")),
            AllCurve(Eqn(Call("if",Eqn(s,p),
                Call("mass",Call("nuP",F.Id("continuousCommonFlow")),Call("nativeEndpoint",p,F.Id("b"))),
                Call("mass",Call("nuB",F.Id("continuousCommonFlow")),Call("nativeEndpoint",beta,F.Id("b")))),D(0)),
                ("s","ActivePhase"),("b","Bool")),
            AllCurve(sameX, ("x", "CurveParameter")));
        Formula average = AllCurve(Eqn(Call("averagedCompletion", n),
            Mul(D(1,0,0,0),Call("integralIco", Fraction(D(2,3,9),D(1,0,0,0)),
                Fraction(D(6),D(2,5)),Call("integrand",x,Mul(Call("curveG",x),Call("pow",x,n)))))),
            ("n", "Nat"));
        Formula kp = Add(k, D(1));
        Formula ratio = Fraction(Call("averagedCompletion", Add(k, D(3))), Call("pow", Fraction(D(6), D(2,5)), Add(k, D(3))));
        Formula constant = Fraction(D(4,3,2), D(5));
        Formula formula = AllCurve(Eqn(ratio, Fraction(Mul(constant, Sub(D(1), Call("pow", Fraction(D(2,3,9), D(2,4,0)), kp))), kp)), ("k", "Nat"));
        Formula coefficient = Call("Tendsto", Call("sequence", k, Mul(kp, ratio)), F.Id("atTop"), Call("Nhds", constant));
        Formula residual = AllCurve(Seq(Call("recurrenceResidual", n), Lt, D(0)), ("n", "Nat"));

        return Blocks(
                Paragraph(Text("For x in the original half-open interval [239/1000,6/25), the construction uses q=1944/390625, g=q/x^3, u=1-g-x and v=x/(g+x). The complete p and beta laws include the infinity coordinate, satisfy the original normalization and tail equations, and remain in every original endpoint box with a=1/3, b=2/5, c=9/25 and z=6/25.")),
                Paragraph(Text("realMass(mu,t) denotes mu.real({t}), and singletonMass(mu,x) denotes mu({x}). mass(mu,univ) and mass(mu,tailSet(s,n)) are evaluations at those sets; mass(mu,infinity(s)) and mass(mu,nativeEndpoint(s,b)) are singleton evaluations. integrand(x,f(x)) binds x in the indicated integral or integrability expression. Powers of a CurveParameter use its real value.")),
                Paragraph(Text("Measurable strict splitting means that every measurable E of positive mass has a measurable D contained in E with 0 < mu(D) < mu(E). For each of the two margins and two joint graph measures, recover x from the ratio of consecutive marker-one coordinates of its first descriptor. Push the restriction to E forward through this same recovery map. This finite real measure is dominated by the original uniformReal measure and has null singletons. The integral of 1 over Iio(b) is a continuous primitive, zero at 239/1000 and equal to the entire restricted mass at 6/25. The intermediate value theorem gives a half-mass cut. Pulling this cut back supplies the required measurable subpiece, including for arbitrary measurable E, not only singletons.")),
                Paragraph(Text("On the actual curveUniform conull carrier x < 6/25 and x > 0. Since q=(9/25)(6/25)^3, g=q/x^3 is strictly greater than 9/25. The same strict positive excess holds almost everywhere on its original p descriptor marginal. Apply NativeBorelCEvent.common_flow_event_localization to this continuousCommonFlow: its actual eventProbability is startedC(continuousCommonFlow,Q)(summableExcess), and nonzero event probability would force excess(Q)=0. Hence this original summable-excess event has probability zero at almost every actual p descriptor. The acquired kernels still retain this same x; no event, measure or realization is replaced.")),
                Node("recovered-measurable","recovered_measurable","The Borel recovery map",
                    AllCurve(Call("Measurable",Call("recoveredParameter",s)),("s","ActivePhase")),
                    "The recovery ratio is defined on the entire original regular descriptor carrier. The positive lower cutoff in its denominator makes it Borel in both phases."),
                Node("recovered-curve","recovered_curve","Recovery on the same curve",
                    AllCurve(Eqn(Call("recoveredParameter",s,descriptor),t),("s","ActivePhase"),("t","CurveParameter")),
                    "For every curve parameter, both recovery maps return its real value. This same supplier is used in curve injectivity, the acquired same-parameter successor and measurable splitting."),
                new DocumentBlock.Section(H("The original half-open real carrier"), Blocks(new DocumentBlock.DisplayFormula(Call("AE",F.Id("uniformReal"),x,Call("member",x,
                        Call("Ico",Fraction(D(2,3,9),D(1,0,0,0)),Fraction(D(6),D(2,5)))))), Paragraph(Text("uniformReal is 1000 times Lebesgue measure restricted to Ico(239/1000,6/25). The displayed set has full measure.")))),
                new DocumentBlock.Section(H("Exact real parameter pushforward"), Blocks(new DocumentBlock.DisplayFormula(Eqn(Call("map",F.Id("curveUniform"),F.Id("parameterValue")),F.Id("uniformReal"))), Paragraph(Text("parameterValue is Subtype.val from CurveParameter to the real line. Its pushforward is exactly uniformReal, so the real integrals and parameter integrals use the same original law.")))),
                Node("averaged-parameter","averaged_parameter","The original averaged coordinate as a moment",
                    AllCurve(Eqn(Call("averagedCompletion",n),Call("integral",F.Id("curveUniform"),
                        Call("integrand",t,Mul(Call("curveG",t),Call("pow",t,n))))),("n","Nat")),
                    "The integrand binds t:CurveParameter and uses its real coercion. This exact moment representation is consumed by the averaged formulas, negative recurrence and the arbitrary finite-observer obstruction."),
                Node("moment-integrable","moment_integrable","Every original moment is integrable",
                    AllCurve(Call("Integrable",Call("integrand",t,Mul(Call("curveG",t),Call("pow",t,n))),
                        F.Id("curveUniform")),("n","Nat")),
                    "The integrand binds t:CurveParameter. Every natural power is integrable against the original finite parameter law; this supplies the finite polynomial-moment expansions."),
                new DocumentBlock.Section(H("Strict upper inequality on the actual parameter carrier"), Blocks(new DocumentBlock.DisplayFormula(Call("AE",F.Id("curveUniform"),t,Seq(t,Lt,Fraction(D(6),D(2,5))))), Paragraph(Text("The original half-open carrier excludes the upper endpoint almost everywhere. The conclusion is used by the strict negative recurrence and strict positive excess applications.")))),
                Describe.Lean(DescribeId.Create("continuous-descriptor-family"),
                    DeclarationHandle.Create(Prefix + "continuous_descriptor_family"),
                    H("Complete regular descriptors and residual coordinates"),
                    StatementSource.FromAuthor(Disp(family)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The curve is measurable in the descriptor space. Both acquired residuals are the exact opposite-phase laws on the same parameter, and all finite and infinite coordinates, tails and endpoint boxes are retained."))), DescribeRole.Theorem),
                new DocumentBlock.Section(H("A same-parameter CommonFlow with null singletons"),
                    Blocks(new DocumentBlock.DisplayFormula(graph),
                        Paragraph(Text("The uniform parameter law is pushed forward to both descriptor margins and to both graph measures. Singleton masses vanish for all four measures, including the explicitly quantified nativeEndpoint(s,b) singleton in each phase, while B and A are deterministic only along the same retained parameter x; their return composition is the identity on the curve.")))),
                new DocumentBlock.Section(H("continuous average integral"), Blocks(new DocumentBlock.DisplayFormula(average), Paragraph(Text("The average is 1000 times the Lebesgue integral of g(x)x^n over Ico(239/1000,6/25). This is the exact normalized uniform law on the original half-open interval.")))),
                new DocumentBlock.Section(H("continuous average formula"), Blocks(new DocumentBlock.DisplayFormula(formula), Paragraph(Text("For every tail index k the normalized average has the exact factor (432/5)(1-(239/240)^(k+1))/(k+1).")))),
                new DocumentBlock.Section(H("continuous average coefficient"), Blocks(new DocumentBlock.DisplayFormula(coefficient), Paragraph(Text("The sequence (k+1) times the displayed normalized average converges to 432/5. All four actual measures admit measurable strict splitting, and the same continuous carrier has strict positive excess, as explained above. The obstruction to arbitrary finite COMPLETE realizations is developed from the complete continuous moments and the actual installed-law transfer equation in NativeBorelFiniteCompleteObstruction.")))),
                new DocumentBlock.Section(H("continuous negative recurrence"), Blocks(new DocumentBlock.DisplayFormula(residual), Paragraph(Text("Write m(n)=averagedCompletion(n). Here recurrenceResidual(n) denotes m(n+2)-(2/9+6/25)*m(n+1)+(2/9)*(6/25)*m(n). The exact moment representation and integrability identify it with the integral of curveG(x)*x^n*(x-2/9)*(x-6/25) against the same curveUniform law. On its conull half-open carrier, curveG(x)>0, x>2/9 and x<6/25, so this integrable expression has strictly negative integral for every natural n, including 0, 1 and 2. Failure of this fixed two-root recurrence alone does not exclude every finite carrier; the finite COMPLETE exclusion uses the all-order polynomial-moment argument and actual installed-law transfer in NativeBorelFiniteCompleteObstruction.")))));
    }

    private static DocumentBlock.Describe Node(string id,string name,string title,Formula statement,string text) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula All(Formula body,params (string Name,string Type)[] xs)
    {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
    private static Formula AllCurve(Formula body, params (string Name, string Type)[] xs)
    {
        for (int k = xs.Length - 1; k >= 0; k--)
            body = Seq(Forall, Sp, F.Id(xs[k].Name), Colon, Sp, F.Id(xs[k].Type), Comma, Sp, Open,body,Close);
        return body;
    }

    private static Formula And(params Formula[] xs)
    {
        Formula r = xs[^1];
        for (int k = xs.Length - 2; k >= 0; k--) r = Seq(Open,xs[k],Close,Land,Sp,Open,r,Close);
        return r;
    }

    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula Sub(Formula a, Formula b) => Seq(Open,a,Minus,b,Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
}
