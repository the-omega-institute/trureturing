using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class BeamSplitterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024nongaussian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full bosonic attenuator and the coherent-state output-entropy question.",
        H("BeamSplitter"),
        Blocks(
            Paragraph(Text("The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.")),
            Node("exponentialCoeff", Disp(All("alpha", Complex(), All("n", Nat(), Eqn(Call("exponentialCoeff", A, N), Div(Pow(A,N), C(Rt(Call("toReal",Fact(N))))))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("exponentialVector", Disp(All("alpha", Complex(), Eqn(Call("exponentialVector", A), Call("lp.mk", Lam("n", Nat(), Call("exponentialCoeff", A, N)))))), "lp.mk forms the square-summable vector with the displayed coefficient function; its membership proof uses the complete exponential series. Proof fields are omitted in constructors.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weylVector", Disp(All("alpha", Complex(), All("beta", Complex(), Eqn(Call("weylVector", A, B), Smul(Exp(Sub(Neg(C(Div(Pow(Norm(A),D(2)),D(2)))),Mul(Conj(A),B))),Call("exponentialVector",Add(A,B))))))), "The Weyl action on unnormalized exponential vectors includes its scalar phase and normalization factor.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("displacement", Disp(All("alpha", Complex(), Eqn(Call("displacement", A), Extension(Complex(),Id("exponentialVector"),Lam("beta",Complex(),Call("weylVector",A,B)))))), "extendOfIsometry is Mathlib LinearEquiv.extendOfIsometry: the identity on finitely supported complex coefficient functions extends along the two displayed linearCombination maps. Density and equality of norms are proved in Lean; proof arguments are omitted. This specifies the global displacement on the Hilbert completion.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coherentCoeff", Disp(All("alpha", Complex(), All("n", Nat(), Eqn(Call("coherentCoeff",A,N),Div(Mul(C(Call("Real.exp",Neg(Div(Pow(Norm(A),D(2)),D(2))))),Pow(A,N)),C(Rt(Call("toReal",Fact(N))))))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coherent", Disp(All("alpha", Complex(), Eqn(Call("coherent", A), Call("lp.mk",Lam("n",Nat(),Call("coherentCoeff",A,N)))))), "Every complex alpha gives the normalized coherent vector exp(-|alpha|^2/2) alpha^n/sqrt(n!). The infinite series proves square summability and norm one. The displayed flattened identifiers Realexp and Complexexp denote Mathlib Real.exp and Complex.exp; ComplexofReal denotes Complex.ofReal, Functionconst denotes Function.const, and lpmk denotes lp.mk. Namespace components are retained while punctuation is omitted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tensor", Disp(All("v",HS,All("w",HS,Eqn(Call("tensor",V,W),Call("lp.mk",Lam("n",Nat(),Smul(At(W,N),V))))))), "The second-mode coordinate n is w(n) times the first-mode vector v. The norm and inner product are the Hilbert tensor-product ones.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("exponentialPair", Disp(All("z",Pair(),Eqn(Call("exponentialPair",Z),Call("tensor",Call("exponentialVector",Fst(Z)),Call("exponentialVector",Snd(Z)))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rotate", Disp(All("t",Real(),All("r",Real(),All("z",Pair(),Eqn(Call("rotate",T,R,Z),Call("pair",Sub(Mul(C(T),Fst(Z)),Mul(C(R),Snd(Z))),Add(Mul(C(R),Fst(Z)),Mul(C(T),Snd(Z))))))))), "This real orthogonal rotation fixes the beam-splitter sign convention: creation operators give (t x+r y)^m(-r x+t y)^n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("beamUnitary", Disp(All("t",Real(),All("r",Real(),All("h",Eqn(Add(Pow(T,D(2)),Pow(R,D(2))),D(1)),Eqn(Call("beamUnitary",T,R,Id("h")),Extension(Pair(),Id("exponentialPair"),Lam("z",Pair(),Call("exponentialPair",Call("rotate",T,R,Z))))))))), "The global unitary is the dense isometric extension of the rotation on exponential vectors. extendOfIsometry has the same convention as in displacement; its density and norm-equality proof arguments are omitted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("beamSplitter", Disp(All("eta",Real(),All("hEta",Icc(E),Eqn(Call("beamSplitter",E,HE),Call("beamUnitary",Rt(E),Rt(Sub(D(1),E))))))), "Transmissivity lies in [0,1]. The coefficients are t=sqrt(eta), r=sqrt(1-eta); the unnamed proof argument of beamUnitary, derived from hEta, is omitted under the existing proof-argument convention.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fockPair", Disp(All("m",Nat(),All("n",Nat(),Eqn(Call("fockPair",M,N),Call("tensor",Fock(M),Fock(N)))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fockExpansion", Disp(All("t",Real(),All("r",Real(),All("m",Nat(),All("n",Nat(),Eqn(Call("fockExpansion",T,R,M,N),FockExpansion())))))), "The two finite sums are the binomial expansion with factorial normalization. val is the natural value of a Fin index; NatSub is truncated natural subtraction. Every term has total occupation m+n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("beamUnitary_fock", Disp(All("t",Real(),All("r",Real(),All("h",Eqn(Add(Pow(T,D(2)),Pow(R,D(2))),D(1)),All("m",Nat(),All("n",Nat(),Eqn(Call("beamUnitary",T,R,Id("h"),Call("fockPair",M,N)),Call("fockExpansion",T,R,M,N)))))))), "The global unitary has this Fock action for every pair of natural occupations. Comparing against the total exponential family identifies the finite binomial expansion.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))), []));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("fockatt-beamsplitter-"+name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix+name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula A => Id("alpha");
    private static Formula B => Id("beta");
    private static Formula Conj(Formula x) => Call("conj",x);
    private static Formula Exp(Formula x) => Call("Complex.exp",x);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Id(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(Id(s.Replace(".", "").Replace("_", "")))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Lam(string v, Formula t, Formula b) => Seq(Parenthesized(Seq(Id(v), Colon, t)), Mapsto, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a),b);
    private static Formula Neg(Formula x) => new Formula.Negate(Parenthesized(x));
    private static Formula Smul(Formula a, Formula b) => Call("smul",a,b);
    private static Formula Nat() => Seq(Mathbb,Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(Id("C")));
    private static Formula HS => Call("lp", Call("Function.const", Nat(), Complex()), D(2));
    private static Formula Pair() => Call("Prod",Complex(),Complex());
    private static Formula M => Id("m");
    private static Formula N => Id("n");
    private static Formula V => Id("v");
    private static Formula W => Id("w");
    private static Formula Z => Id("z");
    private static Formula T => Id("t");
    private static Formula R => Id("r");
    private static Formula E => Id("eta");
    private static Formula HE => Id("hEta");
    private static Formula C(Formula x) => Call("Complex.ofReal",x);
    private static Formula Rt(Formula x) => Call("sqrt",x);
    private static Formula Fact(Formula x) => Call("factorial",x);
    private static Formula Val(Formula x) => Call("val",x);
    private static Formula Fst(Formula x) => Call("fst",x);
    private static Formula Snd(Formula x) => Call("snd",x);
    private static Formula Fsum(string v, Formula t, Formula b) => Seq(Sum,Underscore,Grp(Id(v),Colon,t),Parenthesized(b));
    private static Formula Extension(Formula index, Formula v, Formula w) => Call("extendOfIsometry",Call("LinearEquiv.refl",Complex(),Call("Finsupp",index,Complex())),Call("linearCombination",Complex(),v),Call("linearCombination",Complex(),w));
    private static Formula Icc(Formula x) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, Call("Set.Icc", D(0), D(1)));
    private static Formula Fock(Formula n) => Call("lp.single", D(2), n, Call("Complex.ofReal", D(1)));
    private static Formula NS(Formula a, Formula b) => Call("NatSub",a,b);
    private static Formula FockExpansion()
    {
        var i=Val(Id("i")); var j=Val(Id("j"));
        var coeff=Mul(Mul(Mul(Mul(Mul(Mul(Mul(Call("toReal",Call("choose",M,i)),Call("toReal",Call("choose",N,j))),Pow(T,i)),Pow(R,NS(M,i))),Pow(Neg(R),j)),Pow(T,NS(N,j))),Rt(Call("toReal",Fact(Add(i,j))))),Rt(Call("toReal",Fact(Add(NS(M,i),NS(N,j))))));
        return Fsum("i",Call("Fin",Add(M,D(1))),Fsum("j",Call("Fin",Add(N,D(1))),Smul(C(Div(coeff,Mul(Rt(Call("toReal",Fact(M))),Rt(Call("toReal",Fact(N)))))),Call("fockPair",Add(i,j),Add(NS(M,i),NS(N,j))))));
    }
}
