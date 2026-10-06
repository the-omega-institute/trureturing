using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class FixedSourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedSources.";
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
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);

    private static Formula Ex(Formula body,params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula TailPath(Formula s, Formula a, Formula x, Formula q) => And(
        Equal(Call("apply",q,D(0)),s),
        All(Equal(Call("nextGuard",Call("apply",q,I("p")),Call("apply",a,I("p"))),
            Call("some",Call("apply",q,Add(I("p"),D(1))))),B("p",I("Nat"))),
        All(Call("InSupport",Call("apply",q,I("p")),Call("apply",x,I("p"))),B("p",I("Nat"))),
        All(Equal(Call("apply",x,I("p")),Call("branch",Call("apply",a,I("p")),
            Call("apply",x,Add(I("p"),D(1))))),B("p",I("Nat"))));
    private static Formula TailPrefix(Formula w, Formula a) => All(Imp(Call("lt",I("p"),Call("length",w)),
        Equal(Call("apply",a,I("p")),Call("getElem",w,I("p")))),B("p",I("Nat")));
    private static Formula TailFuture(Formula w, Formula a, Formula tail) => All(
        Equal(Call("apply",a,Add(Call("length",w),I("p"))),Call("apply",tail,I("p"))),B("p",I("Nat")));
    private static Formula TailHullSupport => All(Imp(And(Call("le",I("lo"),I("z")),Call("le",I("z"),I("hi"))),
        Call("InSupport",I("s"),I("z"))),B("z",I("Real")));
    private static Formula TailT => Call("CompetingT",I("o"),I("theta"),I("s"),I("Q"),I("V"),I("h"),I("W"));
    private static Formula TailHigh()
    {
        var choices=Call("choiceBlocks",I("R"),I("zs"));var colors=Call("choiceBlocks",I("W"),I("zs"));
        var prefix=Call("append",I("P"),choices);var cs=Call("append",I("h"),colors);var alpha=Call("address",Call("append",prefix,I("w")));
        var record=Call("recordWithTail",I("o"),cs,I("w"));
        var data=And(Call("le",D(0),I("theta")),Call("LegalWord",I("G0"),I("s"),I("P")),Equal(Call("length",I("P")),Call("length",I("h"))),
            All(And(Call("LegalWord",I("s"),I("s"),Call("apply",I("R"),I("i"))),
                Equal(Call("length",Call("apply",I("R"),I("i"))),Call("length",Call("apply",I("W"),I("i"))))),B("i",I("Bool"))),
            Call("lt",I("lo"),I("hi")),TailHullSupport,
            All(Imp(And(Call("le",I("lo"),I("z")),Call("le",I("z"),I("hi"))),
                And(Call("le",I("lo"),Call("compose",Call("apply",I("R"),I("i")),I("z"))),
                    Call("le",Call("compose",Call("apply",I("R"),I("i")),I("z")),I("hi")))),B("i",I("Bool")),B("z",I("Real"))),
            Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),I("P"),I("h")),
            All(Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),Call("apply",I("R"),I("i")),Call("apply",I("W"),I("i"))),B("i",I("Bool"))));
        var result=Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            All(And(Call("OperationRecord",I("o"),I("theta"),I("closed"),alpha,record),Call("OperationFiniteSource",alpha),
                All(Equal(Call("apply",record,Add(Call("length",cs),I("p"))),Call("observe",I("o"),Call("coordinate",I("w"),I("p")),D(0))),B("p",I("Nat")))),
                B("zs",Call("List",I("Bool"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))));
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),B("P",Call("List",I("Label"))),
            B("h",Call("List",I("Color"))),B("R",Fn(I("Bool"),Call("List",I("Label")))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("lo",I("Real")),B("hi",I("Real"))));
    }
    private static Formula TailLow()
    {
        var fv=Call("composeMap",I("V"));var a=I("a");var y=I("y");
        var feasible=Call("ifThenElse",Call("lt",D(0),a),And(Call("Nonempty",TailT),Call("member",y,Call("closure",TailT))),Call("member",y,TailT));
        var data=And(Call("le",D(0),I("theta")),Call("LegalWord",I("G0"),I("s"),I("Q")),Call("LegalWord",I("s"),I("s"),I("V")),
            Equal(Call("length",I("Q")),Call("length",I("h"))),
            All(Equal(Call("length",I("V")),Call("length",Call("apply",I("W"),I("i")))),B("i",I("Bool"))),
            Call("lt",Call("negate",D(1)),a),Call("lt",a,D(1)),Call("notEqual",a,D(0)),
            Equal(a,Pow(Call("negate",I("g")),Call("length",I("V")))),Equal(Call("compose",I("V"),y),y),feasible);
        var prefix=Call("append",I("Q"),Call("choiceBlocks",Call("constantWordFamily",I("V")),I("zs")));
        var cs=Call("append",I("h"),Call("choiceBlocks",I("W"),I("zs")));
        var result=Ex(And(TailPath(I("s"),I("tail"),I("x"),I("path")),
            All(Call("member",Call("iterateApply",fv,I("n"),Call("apply",I("x"),D(0))),TailT),B("n",I("Nat"))),
            All(Ex(And(Call("OperationOmega",I("beta"),I("X")),TailPrefix(prefix,I("beta")),
                TailFuture(prefix,I("beta"),I("tail")),TailFuture(prefix,I("X"),I("x")),
                Call("OperationRecord",I("o"),I("theta"),I("closed"),I("beta"),Call("recordWithOmegaTail",I("o"),cs,I("x")))),
                B("beta",Fn(I("Nat"),I("Label"))),B("X",Fn(I("Nat"),I("Real")))),B("zs",Call("List",I("Bool"))))),
            B("tail",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard"))));
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),
            B("Q",Call("List",I("Label"))),B("V",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("a",I("Real")),B("y",I("Real"))));
    }
    private static Formula TailSynchronous()
    {
        var action=I("action");var initial=I("initialConfiguration");var o=I("o");var theta=I("theta");var n=I("n");var z=I("z");
        var choices=Fn(Call("Fin",n),I("Bool"));var horizon=Add(Call("length",I("P")),Mul(n,I("L")));
        var high=Call("SynchronousHighSource",I("P"),I("U"),z,I("w"));
        var highRecord=Call("recordWithTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("w"));
        var lowRecord=Call("recordWithOmegaTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("x"));
        var beta=Call("apply",I("beta"),z);var cut=Call("apply",I("cuts"),z);var stem=Call("take",I("P"),I("k"));
        var data=And(Call("SynchronousSourceData",o,theta,I("s1"),I("s2"),I("P"),I("Q"),I("h"),I("U"),I("V"),I("W"),
            I("L"),I("lo"),I("hi"),I("a"),I("y"),I("k")),
            Call("ClosedOperationSafety",action,initial,o,theta),Call("ClosedOperationLiveness",action,initial,o,theta),
            Call("ExecutedPostprocessing",action,initial,o,theta));
        var family=And(
            All(And(Call("OperationRecord",o,theta,I("closed"),high,highRecord),Call("OperationFiniteSource",high)),B("z",choices)),
            All(Call("OperationRecord",o,theta,I("closed"),beta,lowRecord),B("z",choices)),
            All(TailPrefix(Call("synchronousPrefix",I("Q"),Call("constantWordFamily",I("V")),z),beta),B("z",choices)),
            All(Equal(Call("apply",beta,Add(horizon,I("p"))),Call("apply",I("eta"),I("p"))),B("z",choices),B("p",I("Nat"))),
            All(Equal(Call("apply",highRecord,Add(horizon,I("p"))),Call("observe",o,Call("coordinate",I("w"),I("p")),D(0))),B("z",choices),B("p",I("Nat"))),
            Call("Injective",Call("SynchronousHighFamily",I("P"),I("U"),n,I("w"))),
            All(And(Call("Cut",action,initial,Call("front",highRecord,horizon),cut),Call("le",Call("length",Call("output",cut)),I("k")),
                Equal(Call("output",cut),Call("take",stem,Call("length",Call("output",cut)))),Call("IsPrefix",Call("output",cut),stem)),B("z",choices)),
            Call("Injective",Call("cutStateOutputMap",I("cuts"))),
            All(new Formula.Logic(Call("member",I("c"),I("states")),FormulaLogicOperator.Iff,
                Ex(Equal(Call("state",cut),I("c")),B("z",choices))),B("c",I("Configuration"))),
            Call("le",Pow(D(2),n),Mul(Call("card",I("states")),Add(I("k"),D(1)))));
        var result=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            All(Ex(family,B("beta",Fn(choices,Fn(I("Nat"),I("Label")))),B("cuts",Fn(choices,Call("Frame",I("Configuration"),I("Label")))),
                B("states",Call("Finset",I("Configuration")))),B("n",I("Nat")))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))),B("eta",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))));
        return Disp(All(Imp(data,result),B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
            B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("theta",I("Real")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Call("List",I("Label"))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("L",I("Nat")),B("lo",I("Real")),B("hi",I("Real")),B("a",I("Real")),B("y",I("Real")),B("k",I("Nat"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-fixed-finite-all-histories"),DeclarationHandle.Create(Prefix+"fixed_finite_tail_all_histories"),
                H("One finite tail supplies all high histories"),StatementSource.FromAuthor(TailHigh()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The numerical hull is nondegenerate, supported and invariant under both legal returns; its stem and return endpoint costs satisfy EndpointCertificate. One finite word w is selected before all Bool choice lists. Each source is address((P++choiceBlocks(R,zs))++w), with the prescribed h++choiceBlocks(W,zs) past followed by the literal zero-error coordinate future of w. Errors are chosen on this same source and are zero after the past. Empty stems and histories remain included. A common positive margin over unbounded histories is not asserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-fixed-omega-all-histories"),DeclarationHandle.Create(Prefix+"fixed_omega_tail_all_histories"),
                H("One lawful Omega tail supplies all rival histories"),StatementSource.FromAuthor(TailLow()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("constantWordFamily(V)(i)=V and composeMap(V)(z)=compose(V,z). The actual fixed-point and slope equations identify the centered affine return. Positive-slope feasibility uses nonempty CompetingT and closure membership of its fixed point; negative-slope feasibility uses actual CompetingT membership. One supported scalar is lifted to one legal tail before all histories. Each finite choice sees only the remaining number of identical V returns, while both distinct W color choices remain in every orbit test. The full CompetingT orbit condition is equivalent to supported terminal coordinates and BlockSupply for every finite Q-prefixed history; the reverse direction extracts Q and both W blocks from those same histories. Every record uses its own actual finite errors and the unchanged zero-error tail future."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-synchronous-common-stem"),DeclarationHandle.Create(Prefix+"original_synchronous_common_stem"),
                H("Literal source construction at every first stem disagreement"),StatementSource.FromAuthor(TailSynchronous()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SynchronousSourceData expands as follows: theta>=0; P and Q are legal G0-to-s1/s2 stems with the same length as h; both U returns and the shared V return are legal and have common positive length L, equal to each W length; U(false) differs from U(true). The supported high hull [lo,hi] has positive width and is invariant under U, with the finite EndpointCertificate for P and each U/W pair. The actual V slope a=(-g)^length(V) is nonzero and lies between -1 and 1, compose(V,y)=y, and the sign-sensitive CompetingT feasibility holds. The stems agree before k<length(P) and differ at k. ClosedOperationSafety and ClosedOperationLiveness quantify all original closed OperationRecords and all primitive Runs; liveness is positionwise on eventual-L0 sources. ExecutedPostprocessing is a finite Drain only after actual executed acquisitions.")),Paragraph(Text("SynchronousHighSource(P,U,z,w)=address(synchronousPrefix(P,U,z)++w), and synchronousPrefix(P,U,z)=P++choiceBlocks(U,List.ofFn(z)); SynchronousHighFamily is this source map. The observation horizon is length(P)+nL. Literal block extraction proves its injection from U(false)!=U(true), without a history-injection premise. Independent lawful zero-error [L0] and [L3] records derive startup, preserving arbitrary k in the target family. cutStateOutputMap(cuts)(z) is the pair of readable state and output at that cut. The actual common-stem theorem gives exactly 2^n<=card(states)*(k+1), with n=0 included. Deriving the canonical hull and its nondegeneracy, the original singleton-return reduction and the necessity of the canonical theta maximum remains additional work; optional original return pieces retain their own selection and whole-prefix conditions."))),DescribeRole.Theorem))));
}
