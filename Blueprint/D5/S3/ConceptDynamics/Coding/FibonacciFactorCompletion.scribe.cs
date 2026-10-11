using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FibonacciFactorCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);

    private static Formula DecoderConfigurationExtraction()
    {
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var model = I("model"); var o = I("o"); var b = I("b"); var contract = I("contract");
        var family = I("family"); var xs = I("xs"); var j = I("j"); var p = I("p");
        var a = I("a"); var r = I("record"); var n = I("n"); var x = I("coordinatePath");
        var path = I("guardPath"); var err = I("error");
        var natColor = new Formula.TypeArrow(I("Nat"), I("Color"));
        var natLabel = new Formula.TypeArrow(I("Nat"), I("Label"));
        Formula Apply(Formula f, Formula at) => Call("apply", f, at);
        Formula Hist(Formula list) => Call("history", model, list);
        Formula Run(Formula h) => Call("foldl", Call("appendOutputStep", I("advance")),
            Call("pair", I("initialConfiguration"), I("initialOutput")), h);
        Formula Out(Formula h) => Call("second", Run(h));
        Formula Front(Formula input) => Call("ofFn", Call("restrict", input, n));
        Formula Source(Formula side) => Call("source", side, model, xs);
        Formula FiniteSource(Formula address) => new Formula.BindMany(FormulaQuantifier.Exists,
            [B("M", I("Nat"))], All(Imp(Call("le", I("M"), p), Equal(Apply(address, p), I("L0"))),
                B("p", I("Nat"))));
        Formula Record(Formula address, Formula input) => new Formula.BindMany(FormulaQuantifier.Exists,
            [B("coordinatePath", new Formula.TypeArrow(I("Nat"), I("Real"))),
             B("guardPath", new Formula.TypeArrow(I("Nat"), I("Guard"))),
             B("error", new Formula.TypeArrow(I("Nat"), I("Real")))], And(
                Equal(Apply(path, D(0)), I("G0")),
                All(Equal(Call("nextGuard", Apply(path, p), Apply(address, p)),
                    Call("some", Apply(path, Add(p, D(1))))), B("p", I("Nat"))),
                All(Call("InSupport", Apply(path, p), Apply(x, p)), B("p", I("Nat"))),
                All(Equal(Apply(x, p), Call("branch", Apply(address, p), Apply(x, Add(p, D(1))))),
                    B("p", I("Nat"))),
                Call("ErrorBound", b, contract, err),
                All(Equal(Call("observe", o, Apply(x, p), Apply(err, p)), Apply(input, p)),
                    B("p", I("Nat")))));
        var output = Out(Front(r));
        var safe = All(Imp(Record(a, r), All(Imp(Call("lt", p, Call("length", output)),
            Equal(Call("get", output, p), Apply(a, p))), B("n", I("Nat")), B("p", I("Nat")))),
            B("a", natLabel), B("record", natColor));
        var live = All(Imp(And(Record(a, r), FiniteSource(a)),
            All(new Formula.BindMany(FormulaQuantifier.Exists, [B("n", I("Nat"))],
                Call("lt", p, Call("length", output))), B("p", I("Nat")))),
            B("a", natLabel), B("record", natColor));
        var supplied = All(Imp(Call("member", xs, family), And(
            Equal(Call("listWeight", xs), I("N")),
            Call("ActualPairSupply", model, o, b, contract, xs))), B("xs", Returns));
        var conclusion = And(
            All(Imp(Call("member", xs, family), All(And(
                Record(Source(j), Call("pairedRecord", model, o, xs, j)), FiniteSource(Source(j))),
                B("j", I("Side")))), B("xs", Returns)),
            All(Imp(Call("member", xs, family), Equal(Out(Hist(xs)), Call("nil", I("Label")))),
                B("xs", Returns)),
            Call("InjectiveOn", Call("runHistory", I("advance"), I("initialConfiguration"),
                I("initialOutput"), model), family),
            Call("InjectiveOn", Call("configurationHistory", I("advance"), I("initialConfiguration"),
                I("initialOutput"), model), family),
            Call("le", Call("card", family), Mul(Call("card", Call("image", family,
                Call("configurationHistory", I("advance"), I("initialConfiguration"),
                    I("initialOutput"), model))), Add(D(0), D(1)))));
        return Disp(All(Imp(And(supplied, safe, live), conclusion),
            B("Configuration", I("Type")),
            B("advance", new Formula.TypeArrow(I("Configuration"), new Formula.TypeArrow(I("Color"),
                Call("Product", I("Configuration"), Call("List", I("Label")))))),
            B("initialConfiguration", I("Configuration")), B("initialOutput", Call("List", I("Label"))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("contract", I("Contract")), B("N", I("Nat")), B("family", Call("Finset", Returns))));
    }

    private static Formula Ex(Formula body,params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula BudgetRange()
    {
        var scale=Mul(Pow(I("g"),D(2)),Pow(I("chi"),I("K")));
        var fixedState=Call("divide",Call("aSide",I("high")),Sub(D(1),Mul(I("rho"),Pow(I("chi"),I("K")))));
        return And(Call("le",D(2),I("K")),
            Call("lt",Sub(I("lam"),Mul(scale,Call("hSide",I("high")))),I("b")),
            Call("lt",I("b"),Sub(I("lam"),Mul(scale,fixedState))));
    }
    private static Formula Threshold => Call("divide",Call("divide",Sub(I("lam"),I("b")),Pow(I("g"),D(2))),Pow(I("chi"),I("K")));
    private static Formula OperationPremises()
    {
        var c=I("Configuration");var nat=I("Nat");var action=I("action");var init=I("initialConfiguration");
        var record=Call("OperationRecord",I("o"),I("b"),I("contract"));
        var r=I("recordInput");var source=I("address");var t=I("t");
        var initial=Call("frame",init,D(0),I("nil"));
        var safe=All(Imp(And(Call("apply",record,source,r),Call("Run",action,Call("full",r),initial,t),
            Call("lt",I("p"),Call("length",Call("output",t)))),Equal(Call("get",Call("output",t),I("p")),Call("apply",source,I("p")))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("t",Call("Frame",c,I("Label"))),B("p",nat));
        var live=All(Imp(And(Call("apply",record,source,r),Call("OperationFiniteSource",source)),
            Ex(And(Call("Run",action,Call("full",r),initial,t),Call("lt",I("p"),Call("length",Call("output",t)))),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("p",nat));
        var f=I("f");var outword=I("outword");var batch=I("batch");var q=I("q");
        var post=All(Imp(And(Call("apply",record,source,r),
            Call("Run",action,Call("full",r),initial,Call("frame",I("c"),q,outword)),
            Equal(Call("apply",action,I("c")),Call("acquire",f)),
            Equal(Call("apply",f,Call("apply",r,q)),Call("some",Call("pair",I("d"),batch)))),
            Ex(Call("Drain",action,Call("frame",I("d"),Add(q,D(1)),Call("append",outword,batch)),t),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("c",c),B("d",c),B("q",nat),
            B("outword",Call("List",I("Label"))),B("batch",Call("List",I("Label"))),
            B("f",Fn(I("Color"),Call("Option",Call("Product",c,Call("List",I("Label")))))));
        return And(BudgetRange(),safe,live,post,
            Call("InjOn",I("encoding"),Call("AllActualReachable",action,init,record)));
    }
    private static Formula CompletePeak => Call("PeakFunction",I("action"),I("initialConfiguration"),
        Call("OperationRecord",I("o"),I("b"),I("contract")),I("encoding"));
    private static Formula PeakRatioLiminf => Call("liminfAtTop",Call("CompletePeakRatio",CompletePeak));
    private static Formula StorageTelescope(Formula body) => Disp(All(Imp(OperationPremises(),body),
        B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
        B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
        B("K",I("Nat")),B("encoding",Fn(I("Configuration"),Call("List",I("Bool"))))));
    private static Formula CompleteStorageRate() => StorageTelescope(All(
        Call("le",Call("ofReal",Call("WeakListRate",I("K"),Threshold,I("sourceModel"))),PeakRatioLiminf),B("sourceModel",I("Model"))));


    private static Formula TailPrefix(Formula w, Formula a) => All(Imp(Call("lt",I("p"),Call("length",w)),
        Equal(Call("apply",a,I("p")),Call("getElem",w,I("p")))),B("p",I("Nat")));
    private static Formula CanonicalHighFixedFiniteTail()
    {
        var u=I("U");var v=I("V");var length=I("L");var lo=Call("canonicalReturnLo",u,length);var hi=Call("canonicalReturnHi",u,length);
        var lowLo=Call("canonicalReturnLo",v,length);var lowHi=Call("canonicalReturnHi",v,length);
        var theta=Call("familyEndpointBudget",I("P"),I("Q"),I("h"),u,v,I("W"),length);
        var costs=Call("familyEndpointCosts",I("P"),I("Q"),I("h"),u,v,I("W"),length);
        var choices=Call("choiceBlocks",u,I("zs"));var colors=Call("choiceBlocks",I("W"),I("zs"));
        var prefix=Call("append",I("P"),choices);var cs=Call("append",I("h"),colors);
        var alpha=Call("address",Call("append",prefix,I("w")));var record=Call("recordWithTail",I("o"),cs,I("w"));
        var word=Call("apply",u,I("i"));var lowWord=Call("apply",v,I("i"));var colorWord=Call("apply",I("W"),I("i"));
        var data=And(Call("LegalWord",I("G0"),I("s1"),I("P")),Call("LegalWord",I("G0"),I("s2"),I("Q")),
            Equal(Call("length",I("P")),Call("length",I("h"))),Equal(Call("length",I("Q")),Call("length",I("h"))),
            Call("lt",D(0),length),
            All(And(Equal(Call("length",word),length),Equal(Call("length",lowWord),length),
                Call("LegalWord",I("s1"),I("s1"),word),Call("LegalWord",I("s2"),I("s2"),lowWord),
                Equal(Call("length",word),Call("length",colorWord))),B("i",I("Bool"))),
            Call("notEqual",Call("apply",u,I("false")),Call("apply",u,I("true"))));
        var tail=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",lo,Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),hi),
            All(And(Call("OperationRecord",I("o"),theta,I("closed"),alpha,record),Call("OperationFiniteSource",alpha),
                All(Equal(Call("apply",record,Add(Call("length",cs),I("p"))),
                    Call("observe",I("o"),Call("coordinate",I("w"),I("p")),D(0))),B("p",I("Nat")))),
                B("zs",Call("List",I("Bool"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))));
        var result=And(Call("le",D(0),theta),Equal(Call("length",costs),Add(Mul(D(2),Call("length",I("h"))),Mul(D(4),length))),
            Call("EndpointCertificate",theta,lowLo,lowHi,I("Q"),I("h")),
            All(Call("EndpointCertificate",theta,lowLo,lowHi,lowWord,colorWord),B("i",I("Bool"))),tail);
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Fn(I("Bool"),Call("List",I("Label")))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("L",I("Nat"))));
    }

    private static Formula CanonicalSynchronous()
    {
        var action=I("action");var initial=I("initialConfiguration");var o=I("o");var theta=I("theta");var n=I("n");var z=I("z");
        var lo=Call("canonicalReturnLo",I("U"),I("L"));var hi=Call("canonicalReturnHi",I("U"),I("L"));
        var lowLo=Call("canonicalReturnLo",I("V"),I("L"));var lowHi=Call("canonicalReturnHi",I("V"),I("L"));
        var a=Pow(Call("negate",I("g")),I("L"));
        var v0=Call("apply",I("V"),I("false"));
        var competing=Call("CompetingT",o,theta,I("s2"),I("Q"),v0,I("h"),I("W"));
        var feasible=Call("ifThenElse",Call("lt",D(0),a),
            And(Call("Nonempty",competing),Call("member",lowLo,Call("closure",competing))),Call("member",lowLo,competing));
        var choices=Fn(Call("Fin",n),I("Bool"));var horizon=Add(Call("length",I("P")),Mul(n,I("L")));
        var high=Call("SynchronousHighSource",I("P"),I("U"),z,I("w"));
        var highRecord=Call("recordWithTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("w"));
        var lowRecord=Call("recordWithOmegaTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("x"));
        var beta=Call("apply",I("beta"),z);var cut=Call("apply",I("cuts"),z);var stem=Call("take",I("P"),I("k"));
        var ui=Call("apply",I("U"),I("i"));var vi=Call("apply",I("V"),I("i"));var wi=Call("apply",I("W"),I("i"));
        var data=And(Call("LegalWord",I("G0"),I("s1"),I("P")),
            Call("LegalWord",I("G0"),I("s2"),I("Q")),Equal(Call("length",I("P")),Call("length",I("h"))),
            Equal(Call("length",I("Q")),Call("length",I("h"))),Call("lt",D(0),I("L")),
            All(And(Call("LegalWord",I("s1"),I("s1"),ui),Call("LegalWord",I("s2"),I("s2"),vi),
                Equal(Call("length",ui),I("L")),Equal(Call("length",vi),I("L")),
                Equal(Call("length",ui),Call("length",wi))),B("i",I("Bool"))),
            Call("notEqual",Call("apply",I("U"),I("false")),Call("apply",I("U"),I("true"))),
            Call("le",Call("familyEndpointBudget",I("P"),I("Q"),I("h"),I("U"),I("V"),I("W"),I("L")),theta),
            Equal(lowLo,lowHi),feasible,Call("lt",I("k"),Call("length",I("P"))),
            All(Imp(Call("lt",I("p"),I("k")),Equal(Call("getElem",I("P"),I("p")),Call("getElem",I("Q"),I("p")))),B("p",I("Nat"))),
            Call("notEqual",Call("getElem",I("P"),I("k")),Call("getElem",I("Q"),I("k"))),
            Call("ClosedOperationSafety",action,initial,o,theta),Call("ClosedOperationLiveness",action,initial,o,theta),
            Call("ExecutedPostprocessing",action,initial,o,theta));
        var family=And(
            All(And(Call("OperationRecord",o,theta,I("closed"),high,highRecord),Call("OperationFiniteSource",high)),B("z",choices)),
            All(Call("OperationRecord",o,theta,I("closed"),beta,lowRecord),B("z",choices)),
            All(TailPrefix(Call("synchronousPrefix",I("Q"),I("V"),z),beta),B("z",choices)),
            All(Equal(Call("apply",beta,Add(horizon,I("p"))),Call("apply",I("eta"),I("p"))),B("z",choices),B("p",I("Nat"))),
            All(Equal(Call("apply",highRecord,Add(horizon,I("p"))),Call("observe",o,Call("coordinate",I("w"),I("p")),D(0))),B("z",choices),B("p",I("Nat"))),
            Call("Injective",Call("SynchronousHighFamily",I("P"),I("U"),n,I("w"))),
            All(And(Call("Cut",action,initial,Call("front",highRecord,horizon),cut),Call("le",Call("length",Call("output",cut)),I("k")),
                Equal(Call("output",cut),Call("take",stem,Call("length",Call("output",cut)))),Call("IsPrefix",Call("output",cut),stem)),B("z",choices)),
            Call("Injective",Call("cutStateOutputMap",I("cuts"))),
            All(new Formula.Logic(Call("member",I("c"),I("states")),FormulaLogicOperator.Iff,
                Ex(Equal(Call("state",cut),I("c")),B("z",choices))),B("c",I("Configuration"))),
            Call("le",Pow(D(2),n),Mul(Call("card",I("states")),Add(I("k"),D(1)))));
        var result=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",lo,Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),hi),
            All(Ex(family,B("beta",Fn(choices,Fn(I("Nat"),I("Label")))),B("cuts",Fn(choices,Call("Frame",I("Configuration"),I("Label")))),
                B("states",Call("Finset",I("Configuration")))),B("n",I("Nat")))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))),B("eta",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))));
        return Disp(All(Imp(data,result),B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
            B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("theta",I("Real")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Fn(I("Bool"),Call("List",I("Label")))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("L",I("Nat")),B("k",I("Nat"))));
    }


    private static Formula CanonicalPeriodicEndpoints()
    {
        var u=I("U");var length=I("L");var word=Call("apply",u,I("i"));
        var amin=Call("apply",u,I("imin"));var amax=Call("apply",u,I("imax"));
        var positive=Call("lt",D(0),Pow(Call("negate",I("g")),length));
        var lowWord=Call("ifThenElse",positive,amin,Call("append",amin,amax));
        var highWord=Call("ifThenElse",positive,amax,Call("append",amax,amin));
        var v0=Call("compose",Call("apply",u,I("false")),D(0));
        var v1=Call("compose",Call("apply",u,I("true")),D(0));
        var data=And(Call("lt",D(0),length),All(Equal(Call("length",word),length),B("i",I("Bool"))),
            All(Call("LegalWord",I("s"),I("s"),word),B("i",I("Bool"))));
        var result=Ex(And(Equal(Call("compose",amin,D(0)),Call("min",v0,v1)),
            Equal(Call("compose",amax,D(0)),Call("max",v0,v1)),
            Call("PeriodicTail",I("s"),lowWord,Call("canonicalReturnLo",u,length)),
            Call("PeriodicTail",I("s"),highWord,Call("canonicalReturnHi",u,length))),
            B("imin",I("Bool")),B("imax",I("Bool")));
        return Disp(All(Imp(data,result),B("s",I("Guard")),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("L",I("Nat"))));
    }

    private static Formula MarginFamilies => Call("Set", Returns);
    private static Formula MarginEquivalence(Formula a, Formula b) => And(Imp(a, b), Imp(b, a));
    private static Formula UniformMarginScale => Mul(Pow(I("g"), D(2)), Pow(I("chi"), I("K")));
    private static Formula UniformMarginTransitionPremises()
    {
        var q = Sub(I("lam"), Mul(UniformMarginScale, Call("hSide", I("high"))));
        var z = Call("divide", Call("aSide", I("high")),
            Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))));
        var psi = Sub(I("lam"), Mul(UniformMarginScale, z));
        return And(Call("le", D(2), I("K")), Call("lt", q, I("b")),
            Call("lt", I("b"), psi));
    }
    private static Formula UniformMarginFamilySupply(Formula eps) =>
        All(Imp(Call("member", I("execution"), I("family")),
            Call("ActualPairSupply", I("model"), I("o"), Sub(I("b"), eps),
                I("closed"), I("execution"))), B("execution", Returns));
    private static Formula UniformMarginFamilyCap() =>
        All(Imp(Call("member", I("execution"), I("family")),
            All(Imp(Call("member", I("a"), I("execution")),
                Call("le", Call("r", I("a")), I("K"))), B("a", I("Return")))),
            B("execution", Returns));
    private static Formula UniformMarginGapSet =>
        Call("actualFamilyHighGaps", I("model"), I("b"), I("K"), I("family"));
    private static Formula UniformMarginGapLowerBound()
    {
        var premise = And(UniformMarginTransitionPremises(), Call("lt", D(0), I("eps")),
            UniformMarginFamilySupply(I("eps")));
        var conclusion = All(Imp(Call("member", I("gap"), UniformMarginGapSet),
            Call("le", Call("divide", I("eps"), UniformMarginScale), I("gap"))),
            B("gap", I("Real")));
        return Disp(All(Imp(premise, conclusion),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies), B("eps", I("Real"))));
    }
    private static Formula UniformMarginIff()
    {
        var uniform = Ex(And(Call("lt", D(0), I("eps")), UniformMarginFamilySupply(I("eps"))),
            B("eps", I("Real")));
        var delta = Call("actualFamilyDelta", I("model"), I("b"), I("K"), I("family"));
        return Disp(All(Imp(And(UniformMarginTransitionPremises(), UniformMarginFamilyCap()),
            MarginEquivalence(uniform, Call("lt", D(0), delta))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies)));
    }

    private static Formula AutomaticMarginG2 => Pow(I("g"), D(2));
    private static Formula AutomaticMarginScale => Mul(AutomaticMarginG2, Pow(I("chi"), I("K")));
    private static Formula AutomaticMarginCost => Call("actualAutomaticCost", I("K"));
    private static Formula AutomaticMarginHighState(Formula prefix) =>
        Call("execute", I("high"), prefix, Call("initial", I("high"), I("model")));
    private static Formula AutomaticMarginActive(Formula exponent, Formula state) =>
        Sub(I("lam"), Mul(Mul(AutomaticMarginG2, Pow(I("chi"), exponent)), state));
    private static Formula AutomaticMarginAnchorCost =>
        Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), Call("xSide", I("high"))));
    private static Formula AutomaticMarginQ => Sub(I("lam"), Mul(AutomaticMarginScale, Call("hSide", I("high"))));
    private static Formula AutomaticMarginPsi => Sub(I("lam"), Mul(AutomaticMarginScale,
        Call("divide", Call("aSide", I("high")),
            Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))))));
    private static Formula AutomaticMarginCap(Formula xs) =>
        All(Imp(Call("member", I("a"), xs), Call("le", Call("r", I("a")), I("K"))),
            B("a", I("Return")));
    private static Formula AutomaticMarginEnvelope()
    {
        var domain = Call("lt", Call("aSide", I("high")), I("D"));
        var stem = Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), I("D")));
        var conclusion = And(Call("lt", AutomaticMarginCost, AutomaticMarginQ),
            Call("le", Sub(I("lam"), I("rho")), AutomaticMarginCost), Call("le", AutomaticMarginAnchorCost, AutomaticMarginCost),
            All(Imp(domain, Call("lt", stem, AutomaticMarginCost)), B("D", I("Real"))),
            All(Imp(And(Call("lt", I("r"), I("K")), domain),
                Call("lt", AutomaticMarginActive(I("r"), I("D")), AutomaticMarginCost)),
                B("r", I("Nat")), B("D", I("Real"))));
        return Disp(All(Imp(Call("le", D(2), I("K")), conclusion), B("K", I("Nat"))));
    }
    private static Formula AutomaticMarginCappedSupplier()
    {
        var split = Equal(I("execution"), Call("append", I("before"),
            Call("cons", I("a"), I("after"))));
        var high = All(Imp(And(split, Equal(Call("r", I("a")), I("K"))),
            Call("lt", AutomaticMarginActive(I("K"), AutomaticMarginHighState(I("before"))), I("budget"))),
            B("before", Returns), B("a", I("Return")), B("after", Returns));
        return Disp(All(Imp(And(Call("le", D(2), I("K")),
            Call("lt", AutomaticMarginCost, I("budget")), AutomaticMarginCap(I("execution")), high),
            Call("ActualPairSupply", I("model"), I("o"), I("budget"),
                I("strict"), I("execution"))),
            B("model", I("Model")), B("o", I("Ownership")), B("K", I("Nat")),
            B("budget", I("Real")), B("execution", Returns)));
    }
    private static Formula AutomaticMarginExactSupply()
    {
        var delta = Call("actualFamilyDelta", I("model"), I("b"), I("K"), I("family"));
        var eps = Call("actualExactFamilyMargin", I("model"), I("b"), I("K"), I("family"));
        var cap = All(Imp(Call("member", I("execution"), I("family")), AutomaticMarginCap(I("execution"))),
            B("execution", Returns));
        var supplied = All(Imp(Call("member", I("execution"), I("family")),
            Call("ActualPairSupply", I("model"), I("o"), Sub(I("b"), eps),
                I("strict"), I("execution"))), B("execution", Returns));
        return Disp(All(Imp(And(Call("le", D(2), I("K")), Call("lt", AutomaticMarginQ, I("b")),
            Call("lt", I("b"), AutomaticMarginPsi), cap, Call("lt", D(0), delta)),
            And(Call("lt", D(0), eps), supplied)),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies)));
    }

    private static Formula PrefixPathEndpoint()
    {
        Formula Imp(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
        var p=I("p");var path=I("path");var a=I("address");var w=I("word");
        return Disp(All(Imp(And(Call("LegalWord",I("s"),I("e"),w),
            Equal(Call("apply",path,D(0)),I("s")),
            All(Equal(Call("nextGuard",Call("apply",path,p),Call("apply",a,p)),
                Call("some",Call("apply",path,Add(p,D(1))))),B("p",I("Nat"))),
            All(Imp(Call("lt",p,Call("length",w)),Equal(Call("apply",a,p),Call("getElem",w,p))),B("p",I("Nat")))),
            Equal(Call("apply",path,Call("length",w)),I("e"))),
            B("s",I("Guard")),B("e",I("Guard")),B("word",Call("List",I("Label"))),
            B("address",new Formula.TypeArrow(I("Nat"),I("Label"))),B("path",new Formula.TypeArrow(I("Nat"),I("Guard")))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-literal-prefix-guard-endpoint"),
                DeclarationHandle.Create(Prefix+"prefix_path_endpoint"),H("The guard after a legal literal prefix"),
                StatementSource.FromAuthor(PrefixPathEndpoint()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual guard path whose initial guard and every prefix label agree with a legal finite word ends at the prescribed terminal guard. Guard-edge determinism then aligns a fixed tail path after every legal prefix."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-high-fixed-finite-tail"),
                DeclarationHandle.Create(Prefix+"canonical_high_fixed_finite_tail"),
                H("The canonical high hull supplies one finite tail for all histories"),
                StatementSource.FromAuthor(CanonicalHighFixedFiniteTail()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two actual high return words differ literally and have the same positive length. The hull endpoints are exactly canonicalReturnLo(U,L) and canonicalReturnHi(U,L). Their width, support and invariance follow from those legal returns. familyEndpointCosts concatenates the indexed endpoint costs for P,h on the U hull, Q,h on the V hull, and each U(i),W(i) and V(i),W(i) pair. Each entry is the maximum of the two endpoint distances max(cut(c)-x,0,x-cut(c+1)) to the closed color interval. There are exactly 2*length(h)+4*L entries. familyEndpointBudget is their fold by max starting at zero. The legal supports and this one computed maximum derive every supported EndpointCertificate; no certificate is supplied as a premise.")),
                    Paragraph(Text("A single finite legal word w is chosen before every finite Bool choice list zs. It lies strictly inside the canonical hull. The actual source is address((P++choiceBlocks(U,zs))++w), and its record is recordWithTail(o,h++choiceBlocks(W,zs),w). The original finite-tail theorem supplies the closed-budget actual record, eventual L0 source and literal zero-error future of this same fixed tail. Empty stems and the empty choice list are included. The finite endpoint maximum is computed and supplies the high actual family. EndpointNecessity.original_fixed_tail_endpoint_budget separately proves necessity for arbitrary fixed literal, scalar and guard tails and membership of that maximum in coefficientField=Q(t); it assumes no tail scalar lies in the canonical hull. The low certificates here are closed constraints and do not by themselves settle actual low endpoint ownership. This high-side statement does not settle the complete original theorem or a common positive margin over unbounded histories."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-synchronous-common-stem"),
                DeclarationHandle.Create(Prefix+"canonical_synchronous_common_stem"),
                H("Canonical legal families supply the arbitrary common-stem count"),
                StatementSource.FromAuthor(CanonicalSynchronous()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U and V are the two actual Bool-indexed legal return families of the same positive length L. U(false) differs from U(true). The high hull is computed from U. Equality of the two canonical V endpoints is equivalent to literal V(false)=V(true), so the common competing return and its fixed point are derived. The actual CompetingT tests every Q suffix and both W color words. Its signed feasibility test uses the canonical low endpoint and a=(-g)^L; positive slope retains a closure limit and negative slope requires actual membership.")),
                    Paragraph(Text("The finite endpoint budget familyEndpointBudget(P,Q,h,U,V,W,L) is at most theta. Its exact indexed costs derive the observed high stem and return certificates. The nonnegative computed budget also derives theta nonnegativity. EndpointNecessity.original_fixed_tail_endpoint_budget supplies the separate arbitrary-fixed-tail necessity and Q(t) membership result. SameStem compares P and Q at every position below k, and DifferentStem compares their labels at k<P.length. getElem denotes literal list extraction. ClosedOperationSafety, ClosedOperationLiveness and ExecutedPostprocessing retain their original actual-record contracts. SynchronousHighSource(P,U,z,w)=address(synchronousPrefix(P,U,z)++w); SynchronousHighFamily is this map on Fin(n)->Bool, and cutStateOutputMap(z)=((cuts(z)).state,(cuts(z)).output).")),
                    Paragraph(Text("One finite high tail and one legal competing Omega tail are fixed before every n. The sources have the actual prescribed prefixes, all histories are acquired on those sources, the high future is the single literal zero-error tail, and literal block extraction gives source injection. Existing common-stem processing then supplies actual cuts and 2^n<=states.card*(k+1), including n=0 and arbitrary supported k. This construction uses the sufficient endpoint bound; its local conclusion is the common-stem count. Necessity is supplied by EndpointNecessity.original_fixed_tail_endpoint_budget. The optional original-piece condition and full auxiliary bilateral/SFT scope require their own hypotheses and conclusions."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-periodic-endpoints"),
                DeclarationHandle.Create(Prefix+"canonical_periodic_endpoints"),
                H("Extremal literal return blocks encode the canonical endpoints"),
                StatementSource.FromAuthor(CanonicalPeriodicEndpoints()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("imin and imax attain the minimum and maximum of the two actual zero-tail translations. For positive signed slope the lower endpoint repeats U(imin), and the upper endpoint repeats U(imax). For negative slope the respective repeating words are U(imin)++U(imax) and U(imax)++U(imin). Their lengths are L or 2L, so the block periods are one or at most two, including equal translations.")),
                    Paragraph(Text("PeriodicTail(s,w,z) means there are label, scalar and guard sequences a,x,path with path(0)=s and x(0)=z, every literal edge legal, every coordinate in that guard's support, and x(p)=branch(a(p),x(p+1)). At each p<length(w), a(p)=w[p]. For every p the label, scalar and guard at p+length(w) equal their values at p. The proof splices one legal block onto a supported tail and repeats the actual finite block itinerary, using the fixed endpoint coordinate and return guard to verify the joining edge. It does not infer this periodicity from an arbitrary lawful_tail witness or claim a finite-D representative for either endpoint."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-complete-storage-liminf"),DeclarationHandle.Create(Prefix+"original_complete_storage_liminf"),
                H("The original weak-list rate is a necessary full-storage lower limit"),StatementSource.FromAuthor(CompleteStorageRate()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("WeakListRate(K,d,sourceModel) is limsup atTop of logb 2 (max 1 (NatCard(WeakCodebook(K,d,sourceModel,n))))/n, with the casts and zero-denominator convention of Lean Real. Every fixed codebook coefficient is bounded by the same full-storage liminf. If that liminf is infinite the result holds directly. Otherwise its finite real value bounds all shifted coefficients. The factor n/(n+C_R) tends to one, and the limsup product inequality recovers the weak-list rate without assuming exact-weight count monotonicity. The preserved anonymous37 equality identifies this rate with the independent factor and original actual contract rates; no rate proof is replaced here.")),
                    Paragraph(Text("The statement concerns the explicit primitive operation presentation and the supplied original complete encoding. Every readable quantity belongs to Configuration; Frame acquisition and output fields are external bookkeeping. An implementation must represent every actual instruction and charged intermediate state at that granularity. Universal correspondence to every prose decoder and independent authored-formula fidelity are separate from this conditional operational mathematics. No single additive constant at the limiting rate and no attaining decoder are asserted."))),DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("fib-actual-decoder-configuration-extraction"),
                DeclarationHandle.Create(Prefix + "actual_decoder_configuration_extraction"),
                H("Complete configurations separate actual paired records"),
                StatementSource.FromAuthor(DecoderConfigurationExtraction()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An acquisition stage takes a complete readable configuration and the next color, performs its finite computation, and returns the next configuration and a finite ordered output batch. All control, counters, timing, positions and readable output-side information belong to Configuration. The transition does not read the cumulative emitted word. appendOutputStep(advance)((q,v),c) is (q',v concatenated with batch), where advance(q,c)=(q',batch). foldl starts at the fixed initial configuration and initial output. runHistory and configurationHistory apply this recurrence to history(model,xs), taking respectively the joint pair and its first component. Safety is required for every supported legal affine source and actual error-bounded record; liveness requires each position, including L0 positions, at a finite acquisition stage of every eventually-L0 source.")),
                    Paragraph(Text("pairedRecord(model,o,xs,j)(p) equals history(model,xs)[p] while p is less than its length M, and equals observe(o,coordinate(tailPrefix(j),p-M),0) thereafter. Its actual error witness, guard path, supported coordinate path and eventual empty tail are constructed from the original paired supply and source reconstruction. Thus the M departures are acquired once, the terminal M is unobserved at the cut, and the original literal future starts there. The original and anchored offsets are 26 and 52; the weight N may be zero or unsupported, and the family may be empty. Every endpoint flag and each original contract remains a parameter.")),
                    Paragraph(Text("The high stem begins with L5 and the low stem with L0, so their actual first differing position is k=0. Safety on both continuations forces the cumulative output at the common departure cut to be empty. In general the prefix factor would be k+1; here it is 0+1. Equal cut configurations therefore give equal joint pairs. Folding either pair along the same high-side literal future gives identical subsequent output. Positionwise finite liveness and safety then equate the two high source addresses, and equal-weight actual address separation recovers the lists. The joint and configuration maps are injective and the number of family members is at most the number of reached complete configurations times one. The emitted word supplies no readable memory. This finite lower bound applies to each compliant transition semantics; it asserts no upper bound on inefficient decoders and no storage-capacity estimate without a configuration encoding."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-automatic-cost-envelope"),
                DeclarationHandle.Create(Prefix + "actual_automatic_cost_envelope"),
                H("The exact three-term automatic bound"),
                StatementSource.FromAuthor(AutomaticMarginEnvelope()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("actualAutomaticCost(K)=max(max(lam-g^2*chi*xSide(high),lam-g^2*chi^(K-1)*aSide(high)),lam-g^6). This is precisely C_auto of the original display. The three entries are the fixed-anchor cost Theta_1, the low-return and stem envelope, and the nonactive-slot bound. For K>=2, chi*h_H<A_H and X_H>A_H give the first two strict comparisons with q_K; g^2*chi^K*h_H<g^6 gives the third. The natural subtraction in K-1 is used only under K>=2.")),
                    Paragraph(Text("Every actual complete state lies above A_H. A stem uses chi*D; every r<K return uses chi^r*D>=chi^(K-1)*D. These inputs strictly exceed chi^(K-1)*A_H and their active costs are below C_auto. The stated scalar bounds are consumed by the capped supplier and the exact-margin theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-capped-strict-supply-of-high-costs"),
                DeclarationHandle.Create(Prefix + "actual_capped_strict_supply_of_high_costs"),
                H("Capped complete sources at every budget above C_auto"),
                StatementSource.FromAuthor(AutomaticMarginCappedSupplier()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only budget>C_auto, the literal cap r<=K, and the active-cost test at each actual r=K position are needed. There is no q_K<budget premise. The exact split before++(a::after) identifies the actual prefix state. Automatic slots pass by the envelope; high positions pass by the supplied strict cost. The resulting ActualPairSupply contains the whole prescribed paired sources and original zero-error futures for arbitrary ownership flags."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-exact-uniform-family-margin"),
                DeclarationHandle.Create(Prefix + "actual_exact_uniform_family_margin"),
                H("The original C_auto-based numerical margin for the whole family"),
                StatementSource.FromAuthor(AutomaticMarginExactSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write G=actualFamilyHighGaps(model,b,K,family), Delta=actualFamilyDelta(model,b,K,family), and c=g^2*chi^K. If G is nonempty, actualExactFamilyMargin is min(b-C_auto,c*Delta.toReal)/2. If G is empty, it is (b-C_auto)/2. Delta is the signed EReal infimum over every actual high position; in the nonempty positive case the proof establishes Delta<top and Delta!=bottom before using toReal. No attained minimum is assumed.")),
                    Paragraph(Text("The same positive epsilon is fixed before all lists and both source sides. In the nonempty case every high gap is at least Delta.toReal. Taking half the displayed minimum leaves strict budget room both above C_auto and above every high active cost. With no high returns the latter condition is vacuous, so the separate original formula applies even if the new budget is below q_K. All slots satisfy strict error bound b-epsilon, which also gives the requested closed bound with that exact epsilon, and the original literal futures have zero error.")),
                    Paragraph(Text("The family remains an arbitrary set of finite return lists, with unbounded exponents m, histories, list depths and weights. Both actual models and every ownership assignment remain parameters. The earlier full-family iff and exact necessary epsilon lower bound are retained. The ownership-sensitive closed high-guard law is unchanged. No original13, original39.4, original39.5 or original39.7 goal is changed or declared settled."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-uniform-margin-gap-lower-bound"),
                DeclarationHandle.Create(Prefix + "actual_uniform_margin_gap_lower_bound"),
                H("The supplied epsilon bounds every actual high-return gap"),
                StatementSource.FromAuthor(UniformMarginGapLowerBound()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("actualFamilyHighGaps(model,b,K,family) is the real set of execute(high,before,initial(high,model))-(lam-b)/g^2/chi^K, for every literal decomposition before++(a::after) belonging to family with a.r=K. Each decomposition selects the actual state before that return. This includes every high-return position of every family list; no return-length, list-depth, weight or family-cardinality bound is imposed.")),
                    Paragraph(Text("The same supplied epsilon is used for every record and both sides. Its closed error budget b-eps is not required as an extra premise to belong to the transition interval. If a control cost exceeded that budget, the complete-boundary inequality D<h_H would permit an intermediate budget strictly above q_K and strictly below both b and that cost. Monotonicity preserves the identical errors, observations and literal futures at that intermediate budget. The existing ownership-sensitive closed guard then contradicts its control cost. Thus the original eps, without shrinking, gives gap>=eps/(g^2*chi^K). This bound is consumed by the family equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-uniform-family-margin-iff"),
                DeclarationHandle.Create(Prefix + "actual_uniform_family_margin_iff"),
                H("Positive extended-real infimum is equivalent to one family margin"),
                StatementSource.FromAuthor(UniformMarginIff()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("actualFamilyDelta is sInf of the image of actualFamilyHighGaps under the signed real inclusion into EReal. Negative gaps are preserved. The empty high-return set has infimum top, namely positive infinity. The family itself may be empty, and a nonempty family may have no high return. No compactness, attained minimum, finite codebook or common weight is assumed.")),
                    Paragraph(Text("ActualUniformFamilyMargin means there exists one real eps>0 such that every execution in family satisfies ActualPairSupply(model,o,b-eps,closed,execution). Unfolding that existing supply predicate, every side has its own error function bounded by b-eps at all natural positions, reads every departure of the complete history from the same sourcePrefix, is zero at and beyond the history length, and gives the original tailPrefix zero-error readout after the observedPrefix. The stem, paid anchor, all repetitions, literal external block order and unchanged eventual-empty tail therefore remain those of the existing source construction.")),
                    Paragraph(Text("The reverse implication directly consumes actual_exact_uniform_family_margin. It chooses the original C_auto-based epsilon for the nonempty or empty actual high-gap set, then uses those same whole-source witnesses with the closed b-eps bound. The exact sufficient-margin supplier remains valid even when that new budget is below q_K. This works for either original or anchored model and every ownership assignment. Individual-record margins and ownership-sensitive equality at the original closed budget remain the separate existing statements.")),
                    Paragraph(Text("The forward implication consumes the exact necessary bound for the original supplied epsilon; the reverse implication consumes the precise two-branch C_auto margin. Together they retain the whole-family infimum criterion. The original13, original39.4, original39.5 and original39.7 targets retain their existing scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classwise deletion and finite exact-weight cardinality applications are separate from the retained run and actual-membership declarations. The finite configuration lower bound uses full actual supply, safety and positionwise liveness. A lower or upper occurrence map alone does not supply a common positive margin for an infinite family.")))));
}
