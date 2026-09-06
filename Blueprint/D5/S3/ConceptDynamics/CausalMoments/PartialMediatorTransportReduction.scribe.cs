using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class PartialMediatorTransportReductionDocument : IScribeDocumentDefinition
{
    private const string Pfx = "D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Z => D(0);
    private static Formula One => D(1);
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open,a,Close,Sp,op,Sp,Open,b,Close);
    private static Formula C(string s, params Formula[] xs)
    {
        var r = new List<Formula> { Operatorname,Grp(V(s)),Open };
        for (int i=0; i<xs.Length; i++) { if(i>0) r.AddRange([Comma,Sp]); r.Add(xs[i]); }
        r.Add(Close); return Seq([..r]);
    }
    private static Formula Quant(Formula op, string names, Formula body)
    {
        var r=new List<Formula>{op,Sp};
        foreach(string n in names.Split(' ')) r.AddRange([V(n),Comma,Sp]);
        r.Add(body); return Seq([..r]);
    }
    private static Formula All(string ns, Formula x)=>Quant(Forall,ns,x);
    private static Formula Ex(string ns, Formula x)=>Quant(Exists,ns,x);
    private static Formula And(params Formula[] xs)=>xs.Length==1?xs[0]:R(xs[0],Land,And(xs[1..]));
    private static Formula Pair(Formula a,Formula b)=>Seq(Open,a,Comma,Sp,b,Close);
    private static Formula P(Formula a,Formula m)=>C("probability",Pair(a,m));
    private static Formula Kernel(Formula o)=>C("HasOutcomeKernel",o,V("probability"));
    private static Formula Marg(Formula p)=>C("HasMediatorMarginals",p,V("control"),V("treated"));
    private static Formula J(Formula p,Formula o)=>C("partialMediatorBenefit",p,o);
    private static Formula L(Formula p)=>C("linearObjective",C("lowerTransportCost",V("probability")),C("mass",p));
    private static Formula U(Formula p)=>C("linearObjective",C("upperTransportCost",V("probability")),C("mass",p));
    private static Formula Valid=>All("index",And(R(Z,Le,C("probability",V("index"))),R(C("probability",V("index")),Le,One)));
    private static Formula SumOver(string n,Formula x)=>Seq(Sum,Underscore,Grp(V(n)),Sp,Open,x,Close);

    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "For binary treatment and outcome with a finite mediator and independent mechanism disturbances, one transportation matrix and two linear inequalities characterize every attainable rational benefit target.",
        H("Exact partial-mediator transport reduction"),
        Blocks(
            Paragraph(Text("Mediator is any finite type with decidable equality. control and treated are FiniteResponseLaw values on Mediator; coupling is such a law on Mediator times Mediator; outcome is such a law on complete tables Bool times Mediator to Bool. probability is a rational success kernel. Expectations below use the existing linearObjective. The direct treatment-to-outcome edge is allowed; there is no exclusion restriction equating the two treatment rows.")),
            Describe.Lean(DescribeId.Create("mediator-marginals"),DeclarationHandle.Create(Pfx+"HasMediatorMarginals"),H("One mediator transport matrix"),
                StatementSource.FromAuthor(Disp(All("coupling control treated",R(Marg(V("coupling")),Leftrightarrow,And(
                    All("m",R(C("leftResponseMarginal",C("mass",V("coupling")),V("m")),Eq,C("mass",V("control"),V("m")))),
                    All("m",R(C("rightResponseMarginal",C("mass",V("coupling")),V("m")),Eq,C("mass",V("treated"),V("m"))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative normalization is supplied by FiniteResponseLaw. All row and column equations constrain the same matrix, rather than separate cellwise maximizers."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("outcome-kernel"),DeclarationHandle.Create(Pfx+"HasOutcomeKernel"),H("Prescribed outcome mechanism kernel"),
                StatementSource.FromAuthor(Disp(All("outcome probability",R(Kernel(V("outcome")),Leftrightarrow,All("a m",R(C("outcomeSuccess",V("outcome"),V("a"),V("m")),Eq,P(V("a"),V("m")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel consists of intervention success probabilities. Observational identification and zero-probability parent cells require separate assumptions."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-response-law"),DeclarationHandle.Create(Pfx+"partialMediatorResponseLaw"),H("Actual common-source counterfactual law"),
                StatementSource.FromAuthor(Disp(All("coupling outcome",R(C("partialMediatorResponseLaw",V("coupling"),V("outcome")),Eq,
                    C("pushforwardResponseLaw",C("productResponseLaw",V("coupling"),V("outcome")),V("responseMap")))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("responseMap((m0,m1),table) is (table(false,m0),table(true,m1)). Both worlds read the same mediator pair and the same outcome table. The product law makes only the two mechanisms independent."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-benefit"),DeclarationHandle.Create(Pfx+"partialMediatorBenefit"),H("Benefit under the independent source law"),
                StatementSource.FromAuthor(Disp(All("coupling outcome",R(J(V("coupling"),V("outcome")),Eq,C("linearObjective",V("benefitEvent"),C("mass",C("productResponseLaw",V("coupling"),V("outcome")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("benefitEvent is the indicator that responseMap is (false,true). It is evaluated on the complete product source, not declared to equal a transport objective."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("response-bridge"),DeclarationHandle.Create(Pfx+"partialMediatorBenefit_actual_response"),H("Bind to the existing causal benefit readout"),
                StatementSource.FromAuthor(Disp(All("coupling outcome",R(J(V("coupling"),V("outcome")),Eq,C("benefitResponseMass",C("mass",C("partialMediatorResponseLaw",V("coupling"),V("outcome")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof uses the existing deterministic-pushforward expectation identity and the actual 01 response cell."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilinear-cell-decomposition"),DeclarationHandle.Create(Pfx+"partialMediatorBenefit_eq_cells"),H("Derive the bilinear mechanism decomposition"),
                StatementSource.FromAuthor(Disp(All("coupling outcome",R(J(V("coupling"),V("outcome")),Eq,
                    SumOver("pair",R(C("outcomeBenefitCell",V("outcome"),C("fst",V("pair")),C("snd",V("pair"))),Cdot,C("mass",V("coupling"),V("pair")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite independent-product sum is expanded without discarding the common mediator coupling."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lower-cost"),DeclarationHandle.Create(Pfx+"lowerTransportCost"),H("Lower transport cost"),
                StatementSource.FromAuthor(Disp(All("probability pair",R(C("lowerTransportCost",V("probability"),V("pair")),Eq,C("max",Z,R(P(V("true"),C("snd",V("pair"))),Minus,P(V("false"),C("fst",V("pair"))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the lower Boolean response-cell bound at the two mediator values."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper-cost"),DeclarationHandle.Create(Pfx+"upperTransportCost"),H("Upper transport cost"),
                StatementSource.FromAuthor(Disp(All("probability pair",R(C("upperTransportCost",V("probability"),V("pair")),Eq,C("min",R(One,Minus,P(V("false"),C("fst",V("pair")))),P(V("true"),C("snd",V("pair")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost is multiplied by one globally feasible transport matrix. There is no substitution of an independently maximized mediator cell."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transport-bounds"),DeclarationHandle.Create(Pfx+"partialMediatorBenefit_transport_bounds"),H("Necessary bounds at the actual mediator law"),
                StatementSource.FromAuthor(Disp(All("probability coupling outcome",R(Kernel(V("outcome")),Rightarrow,And(R(L(V("coupling")),Le,J(V("coupling"),V("outcome"))),R(J(V("coupling"),V("outcome")),Le,U(V("coupling")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weights are nonnegative and every outcome-law cell obeys the already proved bound."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("simultaneous-endpoint-mechanisms"),DeclarationHandle.Create(Pfx+"simultaneous_transport_endpoint_mechanisms"),H("Common mechanisms attain both costs"),
                StatementSource.FromAuthor(Disp(All("probability",R(Valid,Rightarrow,Ex("lower upper",And(Kernel(V("lower")),Kernel(V("upper")),All("coupling",And(R(J(V("coupling"),V("lower")),Eq,L(V("coupling"))),R(J(V("coupling"),V("upper")),Eq,U(V("coupling"))))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two outcome laws are selected before all mediator couplings. This discharges simultaneous attainability rather than assuming that individual cell bounds can be combined."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-coupling-image"),DeclarationHandle.Create(Pfx+"fixed_coupling_benefit_sharp_iff"),H("Full rational interval at one mediator coupling"),
                StatementSource.FromAuthor(Disp(All("probability coupling target",R(Valid,Rightarrow,R(Ex("outcome",And(Kernel(V("outcome")),R(J(V("coupling"),V("outcome")),Eq,V("target")))),Leftrightarrow,And(R(L(V("coupling")),Le,V("target")),R(V("target"),Le,U(V("coupling"))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Interior targets mix only the two complete outcome laws, with the mediator law fixed. Rational interpolation covers endpoints and the zero-width case while retaining mechanism independence."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-transport-reduction"),DeclarationHandle.Create(Pfx+"partial_mediator_target_iff_transport"),H("Exact transportation-LP characterization"),
                StatementSource.FromAuthor(Disp(All("control treated probability target",R(Valid,Rightarrow,R(
                    Ex("coupling outcome",And(Marg(V("coupling")),Kernel(V("outcome")),R(J(V("coupling"),V("outcome")),Eq,V("target")))),Leftrightarrow,
                    Ex("coupling",And(Marg(V("coupling")),R(L(V("coupling")),Le,V("target")),R(V("target"),Le,U(V("coupling")))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The right side has m-squared coupling variables and linear row, column and target conditions. No outcome-law optimization, independent pairwise witnesses, or optimizer-existence premise remains."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("endpoint-transfer"),DeclarationHandle.Create(Pfx+"transport_endpoints_are_causal_sharp"),H("Transport optima give causal endpoint witnesses"),
                StatementSource.FromAuthor(Disp(EndpointFormula())),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lowerCoupling and upperCoupling are actual probability laws with the displayed marginals. The premise includes their transport objective values and universal transport bounds. The conclusion gives universal causal bounds and actual outcome mechanisms attaining both endpoints with those same couplings."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absolute-distance-costs"),DeclarationHandle.Create(Pfx+"transport_cost_absolute_distance_identities"),H("One-dimensional absolute-distance cost identities"),
                StatementSource.FromAuthor(Disp(All("probability coupling",And(
                    R(R(D(2),Cdot,L(V("coupling"))),Eq,R(R(V("mean1"),Minus,V("mean0")),Plus,V("distance01"))),
                    R(R(D(2),Cdot,U(V("coupling"))),Eq,R(R(R(One,Minus,V("mean0")),Plus,V("mean1")),Minus,V("distanceComplement"))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("mean0 and mean1 abbreviate coupling expectations of probability(false,pair.first) and probability(true,pair.second). distance01 is the expectation of their absolute difference. distanceComplement is the expectation of the absolute value of one minus their sum. These are aliases for the full displayed finite sums in Lean. The theorem itself does not certify a sorting algorithm or invoke a Wasserstein implementation."))),DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        var lc=V("lowerCoupling"); var uc=V("upperCoupling");
        return All("control treated probability lower upper lowerCoupling upperCoupling",R(And(Valid,Marg(lc),Marg(uc),R(L(lc),Eq,V("lower")),R(U(uc),Eq,V("upper")),
            All("coupling",R(Marg(V("coupling")),Rightarrow,And(R(V("lower"),Le,L(V("coupling"))),R(U(V("coupling")),Le,V("upper")))))),Rightarrow,
            And(All("coupling outcome",R(And(Marg(V("coupling")),Kernel(V("outcome"))),Rightarrow,And(R(V("lower"),Le,J(V("coupling"),V("outcome"))),R(J(V("coupling"),V("outcome")),Le,V("upper"))))),
                Ex("outcome",And(Kernel(V("outcome")),R(J(lc,V("outcome")),Eq,V("lower")))),
                Ex("outcome",And(Kernel(V("outcome")),R(J(uc,V("outcome")),Eq,V("upper")))))));
    }
}
