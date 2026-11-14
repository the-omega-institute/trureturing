using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannRouterProfilesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannRouterProfiles.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent heterogeneous records on the actual loaded Hann routers have exactly the active-profile rank, complex kernel and complete fidelity-minimizer fibers.",
        H("Physical router profiles"),
        Blocks(
            Def("internal-router-coordinates", "Router", "Internal router coordinates",
                "Router zero is empty. At a successor, none denotes the root router and some(b,v) "
                + "denotes v in the right child when b is true and the left child otherwise. "
                + "routerLabel reads the router field of the actual nested Tree. Incident and output "
                + "rails are excluded. This indexes every internal router, including those off the programmed path."),
            Def("deepest-router", "deepest", "Deepest physical router",
                "snoc appends a final bit to the existing head-first Address. deepest n u is the actual "
                + "depth-n router reached by the length-n prefix u. In the fully programmed tree for snoc u b, "
                + "its label at deepest n i is encode b if i equals u and wait otherwise. Siblings snoc u false "
                + "and snoc u true agree at every other internal router. Both statements hold at every natural n."),
            Def("loaded-router-label", "loadedLabel", "Actual sequential loading",
                "loadedLabel reads routerLabel after load n n on loading n a bus zero. The existing "
                + "sequential-loading identity identifies this tree with programmed n a n, for every external "
                + "qutrit bus label. Thus no bus label affects the observed router profile."),
            Def("active-profile", "SameProfile", "Active profile equality",
                "A rate q is an arbitrary function on all internal routers. A router is active precisely "
                + "when its rate is less than one. SameProfile requires equality of loadedLabel at every "
                + "active router, allowing the two bus labels to differ. Separates means that this equality "
                + "always forces the two addresses to coincide."),
            Describe.Lean(DescribeId.Create("deepest-activity-characterizes-separation"),
                DeclarationHandle.Create(Module + "profile_separation_iff"),
                H("Exact physical profile separation criterion"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive tree depth n+1, all addresses are distinguished exactly when "
                    + "every depth-n router has rate less than one. Necessity uses two siblings under an "
                    + "inactive deepest router: every other literal router label agrees. Sufficiency "
                    + "observes the deepest router under the first address prefix. Different prefixes "
                    + "give an occupied label versus wait; equal prefixes give the two encoded final bits. "
                    + "No restriction on the real rates is needed for this combinatorial equivalence, so "
                    + "independent rates in the closed unit interval and both endpoints are included. "
                    + "The statement concerns the actual loaded physical coordinates. It does not assert "
                    + "record independence, Gram rank or kernel, simplex optimization, or a noisy-continuation formula."))),
                DescribeRole.Theorem),
            Def("heterogeneous-environment", "Environment", "Independent local environments",
                "Environment n is the function space Router n to Option Qutrit, giving four independent "
                + "coordinates per internal router. The common coordinate is none; some wait, some zero "
                + "and some one are the three literal label coordinates. At each node v, localRecord "
                + "uses sqrt(q(v)) on the common coordinate and sqrt(1-q(v)) on its own label. "
                + "At depth zero the environment is a singleton and the empty tensor product is one."),
            Def("heterogeneous-record", "treeRecord", "Physical tensor records and loading bridge",
                "treeRecord n q t multiplies the original HannRouterDephasing.localRecord over every "
                + "literal routerLabel of t. record n q a uses loadedLabel after the actual load, with "
                + "an arbitrary unobserved qutrit bus. The theorem identifies treeRecord after load "
                + "with record for every bus. Rates are independent functions on Router n, each in "
                + "the closed unit interval. No incident or output rail receives a record."),
            Def("realized-profiles", "Profile", "Realized active profiles and class records",
                "Profile n q is the range of the address-to-label function restricted to nodes with "
                + "q(v)<1. profile is the surjective class map. classRecord selects any representative; "
                + "records of equal profiles coincide because q(v)=1 at all inactive nodes. Thus its "
                + "definition is independent of that selection. Unattained label assignments are absent. "
                + "Equality of classes is exactly SameProfile, even for different external bus labels."),
            Def("physical-profile-gram", "gram", "Complex physical Gram and its kernel",
                "gram(a,b) is the environment sum record(a,e) times conjugate(record(b,e)), in "
                + "density-matrix orientation. All these records are real. A class is sampled by selecting "
                + "its label coordinate at each active node and the common coordinate elsewhere. The "
                + "sample is zero on all other classes and has the strictly positive product of "
                + "sqrt(1-q(v)) over active nodes on its own class. These actual environment coordinates "
                + "prove class-record independence. Mathlib Gram rank and kernel theorems then apply. "
                + "classSum is the sum of arbitrary coefficients over each profile fiber."),
            Def("profile-energy", "classEnergy", "Physical quadratic forms",
                "addressEnergy(p) is the real double sum p(a)p(b)gram(a,b).re. classEnergy(x) is "
                + "the environment sum of normSq of the superposition sum x(c)classRecord(c,e). "
                + "The class records are linearly independent, so this quadratic is strictly positive "
                + "on every nonzero real coefficient vector. The class-mass factorization identifies "
                + "addressEnergy with classEnergy after pushforward."),
            Def("class-probability-laws", "ClassDistribution", "Probability laws and disintegrations",
                "ClassDistribution and AddressDistribution are the bundled Convexity.StdSimplex over "
                + "realized classes and addresses. Their weights are nonnegative and sum to one. "
                + "classMass is the existing simplex map along profile, and its weights are classSum. "
                + "This map is surjective: every class law has a nonnegative disintegration over all "
                + "its address fibers, including when some class weights vanish."),
            Def("heterogeneous-joint-output", "jointOutput", "Actual hold and unchanged ideal continuation",
                "jointOutput pulls the original initialized amplitudes back through the actual load "
                + "and the original HannRouterDephasing.postLoad permutation, then appends treeRecord "
                + "at that physical hold state. postLoad is unchanged: exchange, transport, leaf readout "
                + "and reverse forward. noisyOutput traces the complete independent environment, and "
                + "squaredFidelity is the full physical-State ideal-output expectation. idealOutput, "
                + "outputBasis, Normalized and addressProbability retain their original scalar-module "
                + "definitions; only the router rates and records are heterogeneous. In the formula, "
                + "prehold(n,D,s) abbreviates inverse(load n n)(inverse(postLoad n D)(s)); loadedTree "
                + "abbreviates the tree component of load n n (loading n a bus zero)."),
            Def("input-address-distribution", "inputDistribution", "Arbitrary joint amplitudes and realizable laws",
                "inputDistribution is the address law of any normalized complex address/bus input, "
                + "summing normSq over both bus labels. No product-state assumption is made. "
                + "distributionInput realizes every address law using its nonnegative square roots "
                + "and the clean false bus. Hence minimization over normalized joint inputs and over "
                + "the address simplex have exactly the same class-mass criterion."),
            Def("all-depth-deepest-activity", "DeepestActive", "Full-rank activity criterion",
                "DeepestActive zero q is True. At depth m+1 it means q(deepest m u)<1 for every "
                + "length-m prefix u. Full rank is equivalent to this condition at every depth; "
                + "at zero the rank is one. The proof uses deepest_label to distinguish different "
                + "parents and final bits, and sibling_labels to merge siblings under an inactive "
                + "deepest node. These physical relations feed the Gram-rank conclusion."),
            Describe.Lean(DescribeId.Create("complete-physical-profile-event"),
                DeclarationHandle.Create(Module + "physical_profile_event"),
                H("Complete physical profile, rank, kernel and minimizer event"),
                StatementSource.FromAuthor(FullStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every natural depth, every independent rate in the closed unit interval, every "
                    + "classical memory D and arbitrary complex joint address/bus amplitudes are included. "
                    + "The class simplex is compact and the physical squared-norm objective is continuous. "
                    + "Its midpoint gap is one quarter of the strictly positive quadratic of the difference, "
                    + "so the minimizing class law x is unique. All minimizing address laws are exactly "
                    + "the entire pushforward fiber over x, and the same criterion characterizes all "
                    + "normalized-input fidelity minimizers. No full-support condition is imposed. "
                    + "The generic Gram and simplex arguments are consumed auxiliary reasoning. Leinster, "
                    + "arXiv:0910.0906v4, Theorem 3.1 and Corollary 4.1 give generic optimizer context; "
                    + "no unproved literature premise enters the Lean proof. The result is conditional "
                    + "on the stated independent single router hold and ideal remaining gates. It gives "
                    + "no general nonhomogeneous sharp-minimum algorithm."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);


    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Both(params Formula[] a) => System.Linq.Enumerable.Aggregate(a, And);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(I(x), InMacro, Sp, t), Grp(b));

    private static Formula FullStatement()
    {
        Formula n=I("n"), q=I("q"), d=I("D"), a=I("a"), b=I("b"),
            bus=I("bus"), bp=I("busPrime"), v=I("v"), c=I("c"), e=I("e"),
            t=I("t"), s=I("s"), x=I("x"), y=I("y"), z=I("z"), p=I("p"), r=I("r"),
            psi=I("psi"), phi=I("phi"), ap=I("aPrime"), bit=I("bit"), bitp=I("bitPrime");
        Formula real=I("Real"), complex=I("Complex"), qt=I("Qutrit"), boolean=I("Bool"),
            addr=C("Address",n), routers=C("Router",n), env=C("Environment",n),
            profiles=C("Profile",n,q), state=C("State",n), trees=C("Tree",n),
            ad=C("AddressDistribution",n), cd=C("ClassDistribution",n,q),
            amp=Arr(C("Prod",addr,boolean),complex), k=C("gram",n,q),
            rank=C("rank",k), px=C("profile",n,q,a), py=C("profile",n,q,b);
        Formula W(Formula u) => C("weights",u);
        Formula CE(Formula u) => C("classEnergy",n,q,W(u));
        Formula AE(Formula u) => C("addressEnergy",n,q,W(u));
        Formula Mass(Formula u) => C("classMass",n,q,u);
        Formula Fide(Formula u) => C("squaredFidelity",n,q,d,u);
        Formula Prob(Formula u) => C("addressProbability",n,u);
        Formula Norm(Formula u) => C("Normalized",n,u);
        Formula Ideal(Formula u, Formula at) => C("idealOutput",n,d,u,at);
        Formula IsMinClass(Formula u) => All("z",cd,Le(CE(u),CE(z)));
        Formula IsMinAddress(Formula u) => All("r",ad,Le(AE(u),AE(r)));
        Formula IsMinInput(Formula u) => All("phi",amp,Imp(Norm(phi),
            Le(C("re",Fide(u)),C("re",Fide(phi)))));
        Formula load=All("a",addr,All("bus",qt,Eq(C("treeRecord",n,q,C("loadedTree",n,a,bus)),
            C("record",n,q,a))));
        Formula tensorNorm=All("t",trees,Eq(SumOver("e",env,C("normSq",C("treeRecord",n,q,t,e))),D(1)));
        Formula profileEq=All("a",addr,All("b",addr,All("bus",qt,All("busPrime",qt,
            IffOf(Eq(px,py),All("v",routers,Imp(Lt(App(q,v),D(1)),Eq(
                C("loadedLabel",n,a,bus,v),C("loadedLabel",n,b,bp,v)))))))));
        Formula kernel=All("z",Arr(addr,complex),IffOf(Eq(C("mulVec",k,z),D(0)),
            All("c",profiles,Eq(C("classSum",n,q,z,c),D(0)))));
        Formula factor=All("p",ad,Eq(AE(p),CE(Mass(p))));
        Formula ideal=All("psi",amp,All("s",state,Eq(Ideal(psi,s),
            C("initialized",n,psi,C("prehold",n,d,s)))));
        Formula rho=All("psi",amp,All("a",addr,All("aPrime",addr,All("bit",boolean,All("bitPrime",boolean,
            Eq(C("noisyOutput",n,q,d,psi,C("outputBasis",n,d,C("pair",a,bit)),
                C("outputBasis",n,d,C("pair",ap,bitp))),
                Mul(Mul(App(psi,C("pair",a,bit)),C("conj",App(psi,C("pair",ap,bitp)))),App(k,a,ap))))))));
        Formula fidelity=All("psi",amp,Eq(Fide(psi),C("ofReal",C("addressEnergy",n,q,Prob(psi)))));
        Formula norm=All("psi",amp,Imp(Norm(psi),Both(
            Eq(SumOver("s",state,SumOver("e",env,C("normSq",C("jointOutput",n,q,d,psi,s,e)))),D(1)),
            Eq(SumOver("s",state,C("normSq",Ideal(psi,s))),D(1)))));
        Formula realization=All("p",ad,Both(Norm(C("distributionInput",n,p)),
            Eq(C("inputDistribution",n,C("distributionInput",n,p)),p)));
        Formula minimum=Ex("x",cd,Both(IsMinClass(x),
            All("y",cd,Imp(IsMinClass(y),Eq(y,x))),
            C("Surjective",C("classMass",n,q)),
            All("p",ad,IffOf(IsMinAddress(p),Eq(Mass(p),x))),
            All("psi",amp,Imp(Norm(psi),IffOf(IsMinInput(psi),
                Eq(Mass(C("inputDistribution",n,psi)),x))))));
        Formula conclusions=Both(load,tensorNorm,profileEq,
            C("LinearIndependent",complex,C("classRecord",n,q)),
            Eq(rank,C("card",profiles)),kernel,
            IffOf(Eq(rank,new Formula.Power(D(2),n)),C("DeepestActive",n,q)),
            Imp(Eq(n,D(0)),Eq(rank,D(1))),factor,ideal,rho,fidelity,norm,realization,minimum);
        Formula rates=All("v",routers,Both(Le(D(0),App(q,v)),Le(App(q,v),D(1))));
        return All("n",I("Nat"),All("q",Arr(routers,real),Imp(rates,All("D",Arr(addr,boolean),conclusions))));
    }

    private static Formula Statement()
    {
        Formula n = I("n"), q = I("q"), a = I("a"), ap = I("aPrime"),
            bus = I("bus"), bp = I("busPrime"), v = I("v"), u = I("u");
        Formula depth = new Formula.Binary(n, FormulaBinaryOperator.Add, D(1)),
            routers = C("Router", depth), addresses = C("Address", depth);
        var same = All("v", routers, Imp(Lt(App(q, v), D(1)), Eq(
            C("loadedLabel", depth, a, bus, v), C("loadedLabel", depth, ap, bp, v))));
        var separates = All("a", addresses, All("aPrime", addresses,
            All("bus", I("Qutrit"), All("busPrime", I("Qutrit"), Imp(same, Eq(a, ap))))));
        var deepestActive = All("u", C("Address", n), Lt(App(q, C("deepest", n, u)), D(1)));
        return All("n", I("Nat"), All("q", Arr(routers, I("Real")),
            new Formula.Logic(separates, FormulaLogicOperator.Iff, deepestActive)));
    }
}
