using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class TailGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.";
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
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Ex(Formula body,params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula TailOrbit()
    {
        var t=I("T");var x=I("x");var a=I("a");var y=I("y");
        var f=Call("CenteredAffine",y,a);
        var orbit=All(Call("member",Call("iterateApply",f,I("n"),x),t),B("n",I("Nat")));
        var positive=And(Call("member",x,t),Call("member",y,Call("closure",t)));
        var negative=And(Call("member",x,t),Call("member",Call("apply",f,x),t));
        var criterion=All(new Formula.Logic(orbit,FormulaLogicOperator.Iff,
            Call("ifThenElse",Call("lt",D(0),a),positive,negative)),B("x",I("Real")));
        var nonempty=new Formula.Logic(Ex(orbit,B("x",I("Real"))),FormulaLogicOperator.Iff,
            Call("ifThenElse",Call("lt",D(0),a),And(Call("Nonempty",t),Call("member",y,Call("closure",t))),Call("member",y,t)));
        return Disp(All(Imp(And(Call("OrdConnected",t),Call("lt",Call("negate",D(1)),a),Call("lt",a,D(1)),Call("notEqual",a,D(0))),
            And(criterion,nonempty)),B("T",Call("Set",I("Real"))),B("a",I("Real")),B("y",I("Real"))));
    }

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
    private static Formula TailLawful() => Disp(All(Imp(Call("InSupport",I("s"),I("z")),
        Ex(And(TailPath(I("s"),I("a"),I("x"),I("path")),Equal(Call("apply",I("x"),D(0)),I("z"))),
            B("a",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard"))))),
        B("s",I("Guard")),B("z",I("Real"))));
    private static Formula TailApproximation() => Disp(All(Imp(And(Call("InSupport",I("s"),I("z")),Call("lt",D(0),I("epsilon"))),
        Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),
            Call("lt",Call("abs",Sub(I("z"),Call("coordinate",I("w"),D(0)))),I("epsilon"))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))))),
        B("s",I("Guard")),B("z",I("Real")),B("epsilon",I("Real"))));
    private static Formula TailInterior() => Disp(All(Imp(And(Call("lt",I("lo"),I("hi")),TailHullSupport),
        Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),
            Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            Call("OperationFiniteSource",Call("address",I("w"))),
            Ex(TailPath(I("s"),Call("address",I("w")),Call("coordinateSequence",I("w")),I("path")),
                B("path",Fn(I("Nat"),I("Guard"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))))),
        B("s",I("Guard")),B("lo",I("Real")),B("hi",I("Real"))));
    private static Formula TailPrepend() => Disp(All(Imp(And(Call("LegalWord",I("s"),I("e"),I("w")),
        TailPath(I("e"),I("a"),I("x"),I("path"))),
        Ex(And(TailPath(I("s"),I("beta"),I("X"),I("q")),
            Equal(Call("apply",I("X"),D(0)),Call("compose",I("w"),Call("apply",I("x"),D(0)))),
            TailPrefix(I("w"),I("beta")),TailFuture(I("w"),I("beta"),I("a")),TailFuture(I("w"),I("X"),I("x"))),
            B("beta",Fn(I("Nat"),I("Label"))),B("X",Fn(I("Nat"),I("Real"))),B("q",Fn(I("Nat"),I("Guard"))))),
        B("s",I("Guard")),B("e",I("Guard")),B("w",Call("List",I("Label"))),
        B("a",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard")))));
    private static Formula TailColor(string kind)
    {
        var o=I("o");var c=I("c");var z=I("z");var theta=I("theta");
        var interval=Call("FlagInterval",Sub(Call("cut",Call("val",c)),theta),
            Add(Call("cut",Add(Call("val",c),D(1))),theta),Call("lowerOwned",o,c),Call("upperOwned",o,c),z);
        var owned=Call("OwnedColor",o,theta,c,z);var support=Call("InSupport",I("G0"),z);
        Formula formula;
        if(kind=="cell") formula=new Formula.Logic(Call("Cell",o,c,z),FormulaLogicOperator.Iff,
            Call("FlagInterval",Call("cut",Call("val",c)),Call("cut",Add(Call("val",c),D(1))),
                Call("lowerOwned",o,c),Call("upperOwned",o,c),z));
        else if(kind=="interval") formula=Imp(Call("le",D(0),theta),new Formula.Logic(owned,FormulaLogicOperator.Iff,And(support,interval)));
        else if(kind=="error") formula=Imp(support,new Formula.Logic(owned,FormulaLogicOperator.Iff,
            Ex(And(Call("le",Call("abs",I("error")),theta),Equal(Call("observe",o,z,I("error")),c)),B("error",I("Real")))));
        else formula=Imp(Call("le",D(0),theta),Call("OrdConnected",Call("setOfOwnedColor",o,theta,c)));
        if(kind=="cell") return Disp(All(formula,B("o",I("Ownership")),B("c",I("Color")),B("z",I("Real"))));
        if(kind=="connected") return Disp(All(formula,B("o",I("Ownership")),B("theta",I("Real")),B("c",I("Color"))));
        return Disp(All(formula,B("o",I("Ownership")),B("theta",I("Real")),B("c",I("Color")),B("z",I("Real"))));
    }
    private static Formula TailT => Call("CompetingT",I("o"),I("theta"),I("s"),I("Q"),I("V"),I("h"),I("W"));
    private static Formula TailCompeting(string kind)
    {
        Formula result=kind=="interval" ? Imp(Call("le",D(0),I("theta")),Call("OrdConnected",TailT)) :
            Imp(And(Call("LegalWord",I("G0"),I("s"),I("Q")),Call("LegalWord",I("s"),I("s"),I("V"))),
                new Formula.Logic(Call("member",I("z"),TailT),FormulaLogicOperator.Iff,
                    And(Call("InSupport",I("s"),I("z")),Call("BlockSupply",I("o"),I("theta"),I("false"),I("Q"),I("h"),I("z")),
                        All(Call("BlockSupply",I("o"),I("theta"),I("false"),I("V"),Call("apply",I("W"),I("i")),I("z")),B("i",I("Bool"))))));
        return Disp(All(result,B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),
            B("Q",Call("List",I("Label"))),B("V",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("z",I("Real"))));
    }
    private static Formula TailCertificate() => Disp(All(Imp(And(Call("le",D(0),I("theta")),
        Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),I("w"),I("cs")),
        Call("lt",I("lo"),I("x")),Call("lt",I("x"),I("hi"))),
        Call("BlockSupply",I("o"),I("theta"),I("false"),I("w"),I("cs"),I("x"))),
        B("o",I("Ownership")),B("theta",I("Real")),B("lo",I("Real")),B("hi",I("Real")),
        B("w",Call("List",I("Label"))),B("cs",Call("List",I("Color"))),B("x",I("Real"))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-lawful-tail"),DeclarationHandle.Create(Prefix+"lawful_tail"),
                H("Every supported scalar has one legal itinerary"),StatementSource.FromAuthor(TailLawful()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed branch images cover [-1,phi] at G0 and [-1,t] at G1. The inverse branch (shift(label)-z)/g remains in its next guard support. Iterating supported guard-scalar pairs gives one label sequence, one coordinate sequence and one legal guard path with the requested scalar. Shared branch endpoints remain legal."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-finite-approximation"),DeclarationHandle.Create(Prefix+"finite_approximation"),
                H("Finite legal zero tails approximate every supported scalar"),StatementSource.FromAuthor(TailApproximation()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Truncate the same itinerary after n labels. The exact remaining-coordinate error is (-g)^n*x(n), whose absolute value is at most phi*g^n. Geometric convergence gives every positive tolerance. This density concerns the full guard support; it does not identify that interval with a two-return attractor."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-finite-tail-interior"),DeclarationHandle.Create(Prefix+"finite_tail_interior"),
                H("A finite tail in a supported interval interior"),StatementSource.FromAuthor(TailInterior()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A midpoint approximation within half the interval width yields a finite legal word whose zero-tail scalar lies strictly between lo and hi. coordinateSequence(w)(p)=coordinate(w,p). The full eventually-L0 address and its entire legal supported coordinate path are retained, for either initial guard."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-prepend-legal-tail"),DeclarationHandle.Create(Prefix+"prepend_legal_tail"),
                H("Splicing one fixed legal coordinate tail"),StatementSource.FromAuthor(TailPrepend()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("TailPath(s,a,x,path) means that path starts at s, every label follows nextGuard, every scalar lies in its corresponding support, and every affine recurrence holds. A legal finite prefix prepends exactly its labels and composition value. Both shifted futures are exact, including the recurrence at the splice boundary."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-cell-flag-interval"),DeclarationHandle.Create(Prefix+"cell_flag_interval"),
                H("Exact color cells and all five endpoint flags"),StatementSource.FromAuthor(TailColor("cell")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FlagInterval(lo,hi,left,right,z) is lo<=z<=hi with z=lo implying left and z=hi implying right. lowerOwned is true at color zero and otherwise uses the corresponding true flag; upperOwned is true at color five and otherwise uses the corresponding false flag. These are exactly the original Cell boundaries."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-interval"),DeclarationHandle.Create(Prefix+"owned_color_interval"),
                H("Closed error dilation with actual endpoint ownership"),StatementSource.FromAuthor(TailColor("interval")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OwnedColor(o,theta,c,z) requires z in G0 support and a target u in the actual Cell(o,c) with abs(z-u)<=theta. Dilation shifts the two cell endpoints by theta and retains their original ownership. Support is intersected separately, so clipping an expanded interval does not transfer an unrelated ownership flag to a new boundary. At theta zero the target is z itself."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-error"),DeclarationHandle.Create(Prefix+"owned_color_error"),
                H("Attainable colors are exact observe error outcomes"),StatementSource.FromAuthor(TailColor("error")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For supported z, clipping z+error changes its distance from z by at most abs(error). Conversely a supported target u is fixed by clip and is obtained with error=u-z. This proves both directions of the actual observe relation, including every ownership flag."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-connected"),DeclarationHandle.Create(Prefix+"owned_color_ordConnected"),
                H("Actual attainable color sets are intervals"),StatementSource.FromAuthor(TailColor("connected")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("setOfOwnedColor(o,theta,c) is the set of real z satisfying OwnedColor(o,theta,c,z). Its supported flagged interval is order-connected, including empty sets and excluded endpoints."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-t-connected"),DeclarationHandle.Create(Prefix+"competingT_ordConnected"),
                H("The actual competing-tail intersection is an interval"),StatementSource.FromAuthor(TailCompeting("interval")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CompetingT is the intersection of the terminal guard support, every actual Q-suffix color constraint for r<h.length, and every V-suffix constraint for each of the two W words. Affine preimages preserve order-connectedness for either slope sign. No terminal color test is added."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-t-actual"),DeclarationHandle.Create(Prefix+"competingT_mem_actual"),
                H("Concrete tail membership and actual slot errors"),StatementSource.FromAuthor(TailCompeting("actual")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Legal Q and V words transport support through every suffix. Membership in CompetingT is exactly supported terminal membership and the closed BlockSupply conditions for the stem and both return-color choices."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-certificate-actual-slots"),DeclarationHandle.Create(Prefix+"certificate_actual_slots"),
                H("Finite endpoint costs supply every interior slot"),StatementSource.FromAuthor(TailCertificate()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EndpointCertificate gives supported images of lo and hi at each departure suffix and bounds max(cut(c)-z,0,z-cut(c+1)) by theta at each image. A nonzero literal suffix slope sends an interior scalar strictly between those two endpoint images. This yields actual ownership-sensitive error witnesses at theta, including theta zero."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-tail-orbit-criterion"),DeclarationHandle.Create(Prefix+"competing_tail_orbit_criterion"),
                H("Endpoint-sensitive scalar competing-tail orbits"),StatementSource.FromAuthor(TailOrbit()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CenteredAffine(y,a)(x)=y+a(x-y), and iterateApply(f,n,x)=f^[n](x). T is any order-connected real set, including empty and singleton intervals. For 0<a<1 the full orbit condition is x in T and y in closure(T); membership of y itself is unnecessary. For -1<a<0 it is x in T and f(x) in T; these two actual members also force y in T, and this is equivalent to a nonempty feasible orbit set. Positive iterates converge to y and lie strictly between the initial point and y; negative iterates remain in the closed segment between x and f(x). Actual open and closed endpoint membership is retained.")),
                    Paragraph(Text("This is the scalar interval part of the original39.5 criterion. The concrete owned-color intersection and fixed-tail constructions connect this scalar condition to actual legal source records under their explicit hull and return-map data. An optional original-piece restriction requires a member of the feasible orbit set in that piece and is imposed only when present in the family. Canonical hull nondegeneracy, singleton-return reduction, canonical budget necessity and optional whole-prefix piece conditions remain separate original obligations."))),DescribeRole.Theorem))));
}
