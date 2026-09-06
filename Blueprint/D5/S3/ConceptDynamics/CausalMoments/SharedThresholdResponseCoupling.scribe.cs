using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class SharedThresholdResponseCouplingDocument : IScribeDocumentDefinition
{
    private const string Pfx = "D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Z => D(0);
    private static Formula One => D(1);
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open, a, Close, Sp, op, Sp, Open, b, Close);
    private static Formula C(string s, params Formula[] xs)
    {
        var r = new List<Formula> { Operatorname, Grp(V(s)), Open };
        for (int i = 0; i < xs.Length; i++) { if (i > 0) r.AddRange([Comma, Sp]); r.Add(xs[i]); }
        r.Add(Close); return Seq([..r]);
    }
    private static Formula All(string xs, Formula body)
    {
        var r = new List<Formula> { Forall, Sp };
        foreach (string x in xs.Split(' ')) r.AddRange([V(x), Comma, Sp]);
        r.Add(body); return Seq([..r]);
    }
    private static Formula And(params Formula[] xs)
    {
        var r = new List<Formula>();
        for (int i = 0; i < xs.Length; i++) { if (i > 0) r.AddRange([Sp, Land, Sp]); r.AddRange([Open, xs[i], Close]); }
        return Seq([..r]);
    }
    private static Formula Q(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula K(Formula a, Formula m) => C("count", Pair(a,m));
    private static Formula Prob(Formula a, Formula m) => C("probability", Pair(a,m));
    private static Formula T(Formula u) => C("thresholdOutcomeLaw", V("N"), V("hN"), V("count"), u);
    private static Formula Bounds => And(R(Z,Lt,V("N")),All("index",R(C("count",V("index")),Le,V("N"))));
    private static Formula Lo(Formula p0, Formula p1) => C("max",Z,R(p1,Minus,p0));
    private static Formula Hi(Formula p0, Formula p1) => C("min",R(One,Minus,p0),p1);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One complete outcome mechanism attains every pairwise upper cell at once; another attains every lower cell. This is the constructive prerequisite for an exact mediator transport reduction.",
        H("Simultaneous response-cell attainment"),
        Blocks(
            Paragraph(Text("Mediator is any finite type with decidable equality. Complete outcome tables have type Bool times Mediator to Bool. Both interventions evaluate the same table. The notation thresholdOutcomeLaw includes its positive-denominator proof argument hN. All probabilities and expectations are rational.")),
            Describe.Lean(DescribeId.Create("uniform-threshold-law"), DeclarationHandle.Create(Pfx+"uniformThresholdLaw"), H("One finite disturbance"),
                StatementSource.FromAuthor(Disp(All("N hN u",R(C("mass",C("uniformThresholdLaw",V("N"),V("hN")),V("u")),Eq,Q(One,V("N")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("N is a natural number, hN proves N is positive, and u ranges over Fin N. The defining structure proves nonnegativity and normalization."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-prefix"),DeclarationHandle.Create(Pfx+"uniformThreshold_prefix"),H("Exact prefix probability"),
                StatementSource.FromAuthor(Disp(All("N K hN hK",R(C("linearObjective",C("prefixIndicator",V("K")),C("mass",C("uniformThresholdLaw",V("N"),V("hN")))),Eq,Q(V("K"),V("N")))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("hN proves 0<N and hK proves K<=N. prefixIndicator(K)(u) is one exactly when the natural value of u is smaller than K. The proof counts this entire prefix, not a sample."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("outcome-success"),DeclarationHandle.Create(Pfx+"outcomeSuccess"),H("Actual success expectation"),
                StatementSource.FromAuthor(Disp(All("law a m",R(C("outcomeSuccess",V("law"),V("a"),V("m")),Eq,C("linearObjective",C("successIndicator",V("a"),V("m")),C("mass",V("law"))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("successIndicator(a,m)(table) is one exactly when table(a,m) is true. law is a normalized FiniteResponseLaw on complete outcome tables."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("outcome-benefit-cell"),DeclarationHandle.Create(Pfx+"outcomeBenefitCell"),H("A cross-world benefit cell"),
                StatementSource.FromAuthor(Disp(All("law m0 m1",R(C("outcomeBenefitCell",V("law"),V("m0"),V("m1")),Eq,C("linearObjective",C("benefitIndicator",V("m0"),V("m1")),C("mass",V("law"))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("benefitIndicator(m0,m1)(table) is one exactly when table(false,m0) is false and table(true,m1) is true. This uses two entries of one table law."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threshold-outcome-law"),DeclarationHandle.Create(Pfx+"thresholdOutcomeLaw"),H("Two explicit shared-threshold mechanisms"),
                StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Push uniformThresholdLaw through the complete table readout. The lower witness reads u<count(a,m) in both worlds. The upper witness reads the complement of u<N-count(false,m) in the control world and u<count(true,m) in the treated world. The flag chooses a witness, not an assumption on every admissible outcome mechanism."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threshold-success"),DeclarationHandle.Create(Pfx+"thresholdOutcomeLaw_success"),H("Both mechanisms match all success rows"),
                StatementSource.FromAuthor(Disp(All("N hN count upper a m",R(Bounds,Rightarrow,R(C("outcomeSuccess",T(V("upper")),V("a"),V("m")),Eq,Q(K(V("a"),V("m")),V("N"))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement holds for every mediator value and either witness flag, including probability zero and one."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("upper-cells"),DeclarationHandle.Create(Pfx+"thresholdOutcomeLaw_upper_cells"),H("All upper cells from one law"),
                StatementSource.FromAuthor(Disp(All("N hN count m0 m1",R(Bounds,Rightarrow,R(C("outcomeBenefitCell",T(V("true")),V("m0"),V("m1")),Eq,Hi(Q(K(V("false"),V("m0")),V("N")),Q(K(V("true"),V("m1")),V("N")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two favourable threshold events are nested prefixes of the same disturbance. Their intersection has the smaller mass, simultaneously for every m0,m1."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lower-cells"),DeclarationHandle.Create(Pfx+"thresholdOutcomeLaw_lower_cells"),H("All lower cells from one law"),
                StatementSource.FromAuthor(Disp(All("N hN count m0 m1",R(Bounds,Rightarrow,R(C("outcomeBenefitCell",T(V("false")),V("m0"),V("m1")),Eq,Lo(Q(K(V("false"),V("m0")),V("N")),Q(K(V("true"),V("m1")),V("N")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracting the common-prefix intersection computes every lower cell. No independent disturbance is introduced per mediator pair."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cell-bounds"),DeclarationHandle.Create(Pfx+"outcomeBenefitCell_bounds"),H("Bounds for every complete outcome mechanism"),
                StatementSource.FromAuthor(Disp(All("law m0 m1",And(R(Lo(C("outcomeSuccess",V("law"),V("false"),V("m0")),C("outcomeSuccess",V("law"),V("true"),V("m1"))),Le,C("outcomeBenefitCell",V("law"),V("m0"),V("m1"))),R(C("outcomeBenefitCell",V("law"),V("m0"),V("m1")),Le,Hi(C("outcomeSuccess",V("law"),V("false"),V("m0")),C("outcomeSuccess",V("law"),V("true"),V("m1")))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only nonnegative normalization and the actual Boolean response entries are used for necessity."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("simultaneous-frechet-laws"),DeclarationHandle.Create(Pfx+"simultaneous_frechet_outcome_laws"),H("All finite rational kernels have simultaneous endpoint mechanisms"),
                StatementSource.FromAuthor(Disp(All("probability",R(All("index",And(R(Z,Le,C("probability",V("index"))),R(C("probability",V("index")),Le,One))),Rightarrow,Seq(Exists,Sp,V("lower"),Comma,Sp,V("upper"),Comma,Sp,And(
                    All("a m",R(C("outcomeSuccess",V("lower"),V("a"),V("m")),Eq,Prob(V("a"),V("m")))),
                    All("a m",R(C("outcomeSuccess",V("upper"),V("a"),V("m")),Eq,Prob(V("a"),V("m")))),
                    All("m0 m1",R(C("outcomeBenefitCell",V("lower"),V("m0"),V("m1")),Eq,Lo(Prob(V("false"),V("m0")),Prob(V("true"),V("m1"))))),
                    All("m0 m1",R(C("outcomeBenefitCell",V("upper"),V("m0"),V("m1")),Eq,Hi(Prob(V("false"),V("m0")),Prob(V("true"),V("m1"))))))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof first derives a common positive denominator for the entire finite rational kernel. It then constructs the two actual finite laws. The existential laws precede the universal mediator-pair quantifiers."))),DescribeRole.Theorem))));
}
