using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class AttenuatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024nongaussian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full bosonic attenuator and the coherent-state output-entropy question.",
        H("Attenuator"),
        Blocks(
            Paragraph(Text("The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.")),
            Node("ProbabilityVector", Disp(new Formula.Aligned([All("p",Prob(),Seq(Call("weight",P),Colon,Fn(Nat(),Real()))), All("p",Prob(),All("n",Nat(),Leq(D(0),Call("weight",P,N)))), All("p",Prob(),Call("HasSum",Call("weight",P),D(1)))])), "The structure has precisely the data field weight: Nat -> Real and proof fields nonneg and normalized displayed as separate rows above; its support is unrestricted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("DensityOperator", Disp(new Formula.Aligned([All("rho",State(),Seq(Op(Q),Colon,Ops())), All("rho",State(),Call("IsPositive",Op(Q))), All("rho",State(),Call("HasSum",Lam("n",Nat(),Re(Inner(Fock(N),At(Op(Q),Fock(N))))),D(1)))])), "The structure has precisely the data field operator and proof fields positive and trace_one displayed as separate rows above. For a positive bounded operator, finite full-basis diagonal sum characterizes trace class. No Fock-diagonality assumption is made on inputs.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("outputVector", Disp(ChannelAll(All("q",Triple(),Eqn(Call("outputVector",E,HE,P,Q,Id("q")),Smul(C(Rt(Call("weight",P,Fst(Id("q"))))),At(Call("beamSplitter",E,HE,Call("tensor",At(Call("CFC.sqrt",Op(Q)),Fock(Fst(Snd(Id("q"))))),Fock(Fst(Id("q"))))),Snd(Snd(Id("q"))))))))), "q=(n,m,l) indexes the environment number n, the square-root column m of the input, and the discarded-mode slice l. This is the square-root Kraus realization of Tr_2[U_eta(rho tensor sum_n p_n|n><n|)U_eta^dagger], including off-diagonal inputs.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("attenuatorOperator", Disp(ChannelAll(Eqn(Call("attenuatorOperator",E,HE,P,Q),Call("mixture",Triple(),Lam("q",Triple(),Call("outputVector",E,HE,P,Q,Id("q"))))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("attenuator", Disp(ChannelAll(Eqn(Call("operator",Call("attenuator",E,HE,P,Q)),Call("attenuatorOperator",E,HE,P,Q)))), "The state constructor has this operator field. Summability, positivity and trace one of the full triple-index ensemble are checked in Lean.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pureDensity", Disp(All("v",HS,All("hv",Eqn(Norm(V),D(1)),Eqn(Op(Call("pureDensity",V,Id("hv"))),Rank(V))))), "The normalized vector gives its existing Mathlib rank-one projector as the operator field; positivity and trace-one proofs complete the density structure.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pureOutputVector", Disp(All("eta",Real(),All("hEta",Icc(E),All("p",Prob(),All("v",HS,All("q",Call("Prod",Nat(),Nat()),Eqn(Call("pureOutputVector",E,HE,P,V,Id("q")),Smul(C(Rt(Call("weight",P,Fst(Id("q"))))),At(Call("beamSplitter",E,HE,Call("tensor",V,Fock(Fst(Id("q"))))),Snd(Id("q"))))))))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pureAttenuatorOperator", Disp(All("eta",Real(),All("hEta",Icc(E),All("p",Prob(),All("v",HS,Eqn(Call("pureAttenuatorOperator",E,HE,P,V),Call("mixture",Call("Prod",Nat(),Nat()),Lam("q",Call("Prod",Nat(),Nat()),Call("pureOutputVector",E,HE,P,V,Id("q")))))))))), "The pure-input ensemble agrees with the full square-root attenuator. The environment expansion sums p_n times the partial trace of U_eta(v tensor |n>).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coherent_output_covariance", Disp(All("eta",Real(),All("hEta",Icc(E),All("p",Prob(),All("alpha",Complex(),Eqn(Call("pureAttenuatorOperator",E,HE,P,Call("displacement",A,Fock(D(0)))),Call("conjStarAlgEquiv",Call("displacement",Mul(C(Rt(E)),A)),Call("pureAttenuatorOperator",E,HE,P,Fock(D(0)))))))))), "For every countably supported phase-invariant environment, every coherent input has a displaced vacuum output. The assertion concerns the full operator, including its coherences.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("coherentDensity", Disp(All("alpha",Complex(),Eqn(Op(Call("coherentDensity",A)),Rank(Call("coherent",A))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fockDensity", Disp(All("n",Nat(),Eqn(Op(Call("fockDensity",N)),Rank(Fock(N))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))), []));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("fockatt-attenuator-"+name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix+name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Id(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(Id(s.Replace(".", "").Replace("_", "")))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Lam(string v, Formula t, Formula b) => Seq(Parenthesized(Seq(Id(v), Colon, t)), Mapsto, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Smul(Formula a, Formula b) => Call("smul",a,b);
    private static Formula Nat() => Seq(Mathbb,Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(Id("C")));
    private static Formula HS => Call("lp", Call("Function.const", Nat(), Complex()), D(2));
    private static Formula Triple() => Call("Prod",Nat(),Call("Prod",Nat(),Nat()));
    private static Formula Ops() => Call("ContinuousLinearMap",Complex(),HS,HS);
    private static Formula Prob() => Id("ProbabilityVector");
    private static Formula State() => Id("DensityOperator");
    private static Formula A => Id("alpha");
    private static Formula N => Id("n");
    private static Formula V => Id("v");
    private static Formula E => Id("eta");
    private static Formula HE => Id("hEta");
    private static Formula P => Id("p");
    private static Formula Q => Id("rho");
    private static Formula C(Formula x) => Call("Complex.ofReal",x);
    private static Formula Rt(Formula x) => Call("sqrt",x);
    private static Formula Re(Formula x) => Call("Re",x);
    private static Formula Fst(Formula x) => Call("fst",x);
    private static Formula Snd(Formula x) => Call("snd",x);
    private static Formula Op(Formula x) => Call("operator",x);
    private static Formula Inner(Formula a, Formula b) => Call("inner",Complex(),a,b);
    private static Formula Rank(Formula x) => Call("rankOne",Complex(),x,x);
    private static Formula Icc(Formula x) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, Call("Set.Icc", D(0), D(1)));
    private static Formula Fock(Formula n) => Call("lp.single", D(2), n, Call("Complex.ofReal", D(1)));
    private static Formula ChannelAll(Formula b) => All("eta",Real(),All("hEta",Icc(E),All("p",Prob(),All("rho",State(),b))));
}
