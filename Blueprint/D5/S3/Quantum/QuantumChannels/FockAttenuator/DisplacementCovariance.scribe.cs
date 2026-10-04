using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class DisplacementCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024nongaussian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full bosonic attenuator and the coherent-state output-entropy question.",
        H("DisplacementCovariance"),
        Blocks(
            Paragraph(Text("The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.")),
            Node("mixture", Disp(All("iota",Call("Type"),All("v",Fn(Id("iota"),HS),Eqn(Call("mixture",Id("iota"),V),Tsum("i",Id("iota"),Rank(At(V,Id("i")))))))), "The operator is the unconditional sum of rank-one projectors. In every state construction below, summability follows from summability of squared vector norms.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("purePartialTrace", Disp(All("v",K,Eqn(Call("purePartialTrace",V),Call("mixture",Nat(),Lam("n",Nat(),At(V,N)))))), "For a two-mode pure vector the partial trace over the second mode is the sum of the projectors of all first-mode slices. Matrix elements are checked against the contraction by arbitrary first-mode test vectors.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pairWeyl", Disp(All("a",Pair(),All("z",Pair(),Eqn(Call("pairWeyl",Id("a"),Z),Call("tensor",Call("weylVector",Fst(Id("a")),Fst(Z)),Call("weylVector",Snd(Id("a")),Snd(Z))))))), "The displayed equation specifies the defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pairDisplacement", Disp(All("a",Pair(),Eqn(Call("pairDisplacement",Id("a")),Extension(Pair(),Id("exponentialPair"),Lam("z",Pair(),Call("pairWeyl",Id("a"),Z)))))), "The product displacement is the dense isometric extension of the two-mode Weyl family, using the same extendOfIsometry convention.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("partialTrace_pairDisplacement", Disp(All("a",Pair(),All("w",K,Eqn(Call("purePartialTrace",Call("pairDisplacement",Id("a"),W)),Call("conjStarAlgEquiv",Call("displacement",Fst(Id("a"))),Call("purePartialTrace",W)))))), "A displacement of the discarded mode cancels from every reduced matrix element, while the retained displacement conjugates the reduced operator.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("beam_displacement", Disp(All("t",Real(),All("r",Real(),All("h",Eqn(Add(Pow(T,D(2)),Pow(R,D(2))),D(1)),All("a",Pair(),All("w",K,Eqn(Call("beamUnitary",T,R,Id("h"),Call("pairDisplacement",Id("a"),W)),Call("pairDisplacement",Call("rotate",T,R,Id("a")),Call("beamUnitary",T,R,Id("h"),W))))))))), "The displacement commutation identity holds on the entire two-mode Hilbert completion, by continuity from the total exponential family.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))), []));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("fockatt-displacementcovariance-"+name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix+name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Id(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(Id(s.Replace(".", "").Replace("_", "")))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Lam(string v, Formula t, Formula b) => Seq(Parenthesized(Seq(Id(v), Colon, t)), Mapsto, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a),b);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Nat() => Seq(Mathbb,Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(Id("C")));
    private static Formula HS => Call("lp", Call("Function.const", Nat(), Complex()), D(2));
    private static Formula K => Call("lp", Call("Function.const", Nat(), HS), D(2));
    private static Formula Pair() => Call("Prod",Complex(),Complex());
    private static Formula N => Id("n");
    private static Formula V => Id("v");
    private static Formula W => Id("w");
    private static Formula Z => Id("z");
    private static Formula T => Id("t");
    private static Formula R => Id("r");
    private static Formula Fst(Formula x) => Call("fst",x);
    private static Formula Snd(Formula x) => Call("snd",x);
    private static Formula Rank(Formula x) => Call("rankOne",Complex(),x,x);
    private static Formula Tsum(string v, Formula t, Formula b) => Seq(Sum,Apos,Underscore,Grp(Id(v),Colon,t),Parenthesized(b));
    private static Formula Extension(Formula index, Formula v, Formula w) => Call("extendOfIsometry",Call("LinearEquiv.refl",Complex(),Call("Finsupp",index,Complex())),Call("linearCombination",Complex(),v),Call("linearCombination",Complex(),w));
}
