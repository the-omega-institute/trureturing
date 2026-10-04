using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class ExactRealProbeCostsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact real probes have certificate cost two, deterministic cost three, "
            + "weak random cost one, and strong random cost two.",
        H("Exact Real Probe Costs"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-real-probe-costs"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts.result"),
            H("Sharp certificate and discovery costs"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/ConceptDynamics/magniez2013randomized")),
            Blocks(
                Paragraph(Text("Source is the closed unit interval times Bool. The coordinate "
                    + "and label of s are its first and second projections. Querying a returns "
                    + "the label except at the coordinate, where it flips the bit. History "
                    + "uses the dependent passive history carrier and retains each exact "
                    + "parameter and its response; queryCount counts "
                    + "different parameters. Consistent(h,s) checks every response, and "
                    + "Sound(h,b) requires label b on the entire compatibility fiber.")),
                Paragraph(Text("The Controller, Consistent, distinct-parameter set, queryCount, "
                    + "Run, Correct, and cost are supplied directly by the shared read-only "
                    + "execution core. A Controller maps a finite history to a query, a finite "
                    + "return, or a stall. Run(pi,s,emptyHistory,h,b) is finite execution from the "
                    + "empty history with additional record h and output b. Correct(pi) "
                    + "requires a finite correct run on every source. Runs have no uniform "
                    + "depth bound. Repetition is allowed and charged once; cost is infinite "
                    + "when there is no finite run. worstCost(pi) is the supremum over sources. "
                    + "deterministicValue minimizes it over measurable correct controllers.")),
                Paragraph(Text("The midpoint is 1/2. threeProbe(a,c,d) queries a and c, returns "
                    + "the first response when they agree, and otherwise queries d and returns "
                    + "that response. Every sound certificate needs two distinct parameters. "
                    + "Two parameters avoiding the coordinate certify its label. For a "
                    + "correct controller with first parameter a, a terminal record at (a,true) "
                    + "using only a and c would also match (c,false). This forces a third "
                    + "parameter. The fixed controller at 0,1/2,1 attains the bound.")),
                Paragraph(Text("A random family pi uses one input-independent probability law mu. "
                    + "CorrectAE(mu,pi,s) means almost every seed has a finite correct run on s. "
                    + "Weak(mu,pi) requires this for every source separately; Strong(pi) "
                    + "requires Correct(pi(omega)) at every declared seed. expectedCost(mu,pi,s) "
                    + "is the nonnegative extended integral of the execution cost. The "
                    + "randomizedValue(false) and randomizedValue(true) infima range over all "
                    + "seed spaces, Borel control maps, probability laws, and respectively "
                    + "weak or strong contracts, after taking the supremum over sources.")),
                Paragraph(Text("volumeI is the Lebesgue probability law on the closed unit "
                    + "interval. oneProbe(u) queries u and returns its response. Its error "
                    + "seeds at source s are exactly the singleton coordinate(s), with measure "
                    + "zero. Every declared seed nevertheless has an erroneous source. "
                    + "Zero-query returns cannot lower a weak strategy's expected cost: "
                    + "almost sure correctness at two opposite labels excludes them.")),
                Paragraph(Text("StrongSeed denotes the half-open unit interval subtype [0,1), "
                    + "with the standard subtype measure. shift(u) "
                    + "adds 1/2 below 1/2 and subtracts 1/2 above or at 1/2. strongFamily(u) "
                    + "is threeProbe(u,shift(u),1), and volumeJ is its Lebesgue probability law. "
                    + "Every seed is correct on every source. The cost is two except when "
                    + "the coordinate equals u or shift(u), when it is three. For a fixed "
                    + "source the exceptional seeds form a finite null set. Thus its expected "
                    + "cost is two, whereas every fixed seed has worst cost three.")),
                Paragraph(Text("ErrorSeeds(pi,s) is the set of seeds with a finite erroneous "
                    + "return. MeasurableStrategy requires Borel control on the product of "
                    + "seeds and each finite record space, and measurable costs, termination "
                    + "events, and error events for each source. ControlsMeasurably is its "
                    + "control condition. constantFamily(pi) is the constant family on Unit. "
                    + "jointResponse(a,s) is response(a,s), on the product domain. Both "
                    + "attaining families and the joint response satisfy these Borel conditions. "
                    + "The fixed-input expectation convention is acknowledged from Magniez "
                    + "and coauthors; the exact probe sharp values are repository deductions."))),
            DescribeRole.Theorem))));

    private static Formula App(string name, params Formula[] args) => Call(name, args);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Forall(string name, string type, Formula body) =>
        Forall(name, F.Id(type), body);
    private static Formula Exists(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), F.Id(type), body);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = And(clauses[i], result);
        return result;
    }
    private static Formula RandomLower(bool strong)
    {
        var omega = F.Id("Omega");
        var mu = F.Id("mu");
        var pi = F.Id("pi");
        var s = F.Id("s");
        var contract = strong ? App("Strong", pi) : App("Weak", mu, pi);
        return Forall("Omega", "Type", Forall("m", App("MeasurableSpace", omega),
            Forall("mu", App("Measure", omega), Implies(App("IsProbabilityMeasure", mu),
                Forall("pi", new Formula.TypeArrow(omega, F.Id("Controller")),
                    Implies(contract, Forall("s", "Source",
                        Le(Num(strong ? 2 : 1), App("expectedCost", mu, pi, s)))))))));
    }
    private static Formula Statement()
    {
        var s = F.Id("s");
        var h = F.Id("h");
        var b = App("label", s);
        var pi = F.Id("pi");
        var u = F.Id("u");
        var one = F.Id("oneProbe");
        var strong = F.Id("strongFamily");
        var muI = F.Id("volumeI");
        var muJ = F.Id("volumeJ");
        var certificates = Forall("s", "Source", And(
            Forall("h", "History", Implies(App("Consistent", h, s),
                Implies(App("Sound", h, b), Le(Num(2), App("queryCount", h))))),
            Exists("h", "History", All(App("Consistent", h, s), App("Sound", h, b),
                Equal(App("queryCount", h), Num(2))))));
        var lower = Forall("pi", "Controller", Implies(App("Correct", pi),
            Exists("s", "Source", Exists("h", "History", And(
                App("Run", pi, s, F.Id("emptyHistory"), h, b),
                Le(Num(3), App("queryCount", h)))))));
        var triple = App("threeProbe", Num(0), F.Id("midpoint"), Num(1));
        var upper = Forall("s", "Source", Exists("h", "History", And(
            App("Run", triple, s, F.Id("emptyHistory"), h, b), Le(App("queryCount", h), Num(3)))));
        return Disp(All(certificates, lower, App("Correct", triple), upper,
            Equal(F.Id("deterministicValue"), Num(3)), Equal(App("worstCost", triple), Num(3)),
            RandomLower(false), Forall("s", "Source", And(App("CorrectAE", muI, one, s),
                Equal(App("expectedCost", muI, one, s), Num(1)))),
            Forall("u", "StrongSeed", App("Correct", App("strongFamily", u))),
            RandomLower(true), App("IsProbabilityMeasure", muJ),
            Forall("s", "Source", Equal(App("expectedCost", muJ, strong, s), Num(2))),
            App("MeasurableStrategy", one), App("MeasurableStrategy", strong),
            Equal(App("randomizedValue", F.Id("false")), Num(1)),
            Equal(App("randomizedValue", F.Id("true")), Num(2)),
            Forall("s", "Source", Equal(App("ErrorSeeds", one, s),
                new Formula.SetLiteral([App("coordinate", s)]))),
            Forall("u", "UnitInterval", new Formula.Not(App("Correct", App("oneProbe", u)))),
            Forall("u", "StrongSeed", Equal(App("worstCost", App("strongFamily", u)), Num(3))),
            App("ControlsMeasurably", App("constantFamily", triple)),
            App("Measurable", F.Id("jointResponse"))));
    }
}
