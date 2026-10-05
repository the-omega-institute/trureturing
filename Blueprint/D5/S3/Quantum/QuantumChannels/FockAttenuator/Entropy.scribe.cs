using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class EntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.";
    private static readonly LibraryNoteRef EntropySource = LibraryNoteRef.Create("D5/L/QuantumStates/wehrl1978entropy");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full bosonic attenuator and the coherent-state output-entropy question.",
        H("Entropy"),
        Blocks(
            Paragraph(Text("The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.")),
            Node("finiteDiagonal", Disp(All("N",Nat(),All("p",Fn(Call("Fin",Id("N")),Real()),Eqn(Call("finiteDiagonal",Id("N"),P),Fsum("k",Call("Fin",Id("N")),Call("smul",Call("Complex.ofReal",At(P,Id("k"))),Call("rankOne",Complex(),Fock(Call("val",Id("k"))),Fock(Call("val",Id("k")))))))))), "The finite diagonal operator is the sum of p(k) times the occupation rank-one projector. Its definition allows arbitrary real entries; the entropy theorem supplies the bounds from zero to one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(EntropySource)),
            Node("basisEntropy", Disp(All("T",Ops(),All("b",Call("HilbertBasis",Nat(),Complex(),HS),Eqn(Call("basisEntropy",Id("T"),Id("b")),Tsum("n",Nat(),Call("ENNReal.ofReal",Call("negMulLog",Re(Inner(At(Id("b"),N),At(Id("T"),At(Id("b"),N))))))))))), "negMulLog(x)=-x log(x), with its continuous value zero at x=0. ENNReal.ofReal embeds a nonnegative real in the extended nonnegative reals; Complex.ofReal embeds a real scalar in Complex; on a density operator every diagonal probability lies in [0,1]. Natural logarithms give nats.", DescribeRole.Definition, AssessedProvenance.FromLiterature(EntropySource)),
            Node("vonNeumannEntropy", Disp(All("T",Ops(),Eqn(Call("vonNeumannEntropy",Id("T")),Call("iInf",Lam("b",Call("HilbertBasis",Nat(),Complex(),HS),Call("basisEntropy",Id("T"),Id("b"))))))), "The definition is the infimum over complete countable orthonormal bases of the diagonal Shannon entropy. Its equality with spectral von Neumann entropy for every density operator is literature-attested, following the eigenbasis and concavity characterization in Wehrl. The infinite-dimensional equivalence is not kernel-proved here. The kernel proves the finite diagonal spectral formula; the final refutation supplies the needed unitary invariance by transporting all Hilbert bases.", DescribeRole.Definition, AssessedProvenance.FromLiterature(EntropySource)),
            Node("finiteDiagonal_entropy", Disp(All("N",Nat(),All("p",Fn(Call("Fin",Id("N")),Real()),Imp(And(All("j",Call("Fin",Id("N")),Leq(D(0),At(P,Id("j")))),All("j",Call("Fin",Id("N")),Leq(At(P,Id("j")),D(1)))),Eqn(Call("vonNeumannEntropy",Call("finiteDiagonal",Id("N"),P)),Call("ENNReal.ofReal",Call("shannonEntropy",Call("Fin",Id("N")),P))))))), "Concavity of -x log(x), the subprobability row bound and the Parseval column sums give the lower bound in every complete basis. The occupation basis attains it. shannonEntropy is the frozen finite Shannon functional, sum_j negMulLog(p_j). The result does not require the finite entries to sum to one.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(EntropySource))), []));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("fockatt-entropy-"+name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix+name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Id(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(Id(s.Replace(".", "").Replace("_", "")))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Lam(string v, Formula t, Formula b) => Seq(Parenthesized(Seq(Id(v), Colon, t)), Mapsto, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Nat() => Seq(Mathbb,Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(Id("C")));
    private static Formula HS => Call("lp", Call("Function.const", Nat(), Complex()), D(2));
    private static Formula Ops() => Call("ContinuousLinearMap",Complex(),HS,HS);
    private static Formula N => Id("n");
    private static Formula P => Id("p");
    private static Formula Re(Formula x) => Call("Re",x);
    private static Formula Inner(Formula a, Formula b) => Call("inner",Complex(),a,b);
    private static Formula Tsum(string v, Formula t, Formula b) => Seq(Sum,Apos,Underscore,Grp(Id(v),Colon,t),Parenthesized(b));
    private static Formula Fsum(string v, Formula t, Formula b) => Seq(Sum,Underscore,Grp(Id(v),Colon,t),Parenthesized(b));
    private static Formula Fock(Formula n) => Call("lp.single", D(2), n, Call("Complex.ofReal", D(1)));
}
