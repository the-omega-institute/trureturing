using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LocalPerceptionMerminDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/LocalPerceptionMermin.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/ray2025localperception");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four positive context tables with shared singleton means obey the sharp termwise Mermin local-perception bound, after exact elimination of the pair moments.",
        H("The termwise Mermin local-perception bound"), Blocks(
            Node("avg", "Finite expectation", "The finite sum of p(i) f(i). Normalization and nonnegativity are hypotheses of the bound, not part of this definition.", DescribeRole.Definition),
            Node("avg4", "Independent context expectation", "The fourfold sum with weight p(i) q(j) r(k) s(l). These independently drawn context samples form an auxiliary mathematical construction; no original all-settings joint distribution is assumed.", DescribeRole.Definition),
            Node("classical_bound", "The classical bound for real contractions", "For a,A,b,B,c,C in [-1,1], a b c - a B C - A b C - A B c is at most two. The proof interpolates four of the variables between their endpoints and checks the remaining linear bounds. This consumed helper supplies the pointwise inequality in table_bound.", DescribeRole.Theorem),
            Node("edge", "The tetrahedron of contexts", "The four rows label settings A0,B0,C0; A0,B1,C1; A1,B0,C1; A1,B1,C0. Settings have labels 0,1,2,3,4,5 in order A0,A1,B0,B1,C0,C1. Every setting belongs to exactly two contexts.", DescribeRole.Definition),
            Node("triple", "The context triple moment", "The expectation of the product of the three bounded outputs in the indicated context.", DescribeRole.Definition),
            Node("witness", "Squared marginal weights", "The termwise witness is (m0 m2 m4)^2 t0 - (m0 m3 m5)^2 t1 - (m1 m2 m5)^2 t2 - (m1 m3 m4)^2 t3. For the product observable A tensor B tensor C, Ray Eq. (52) gives b c A, a c B, and a b C, whose tensor product has coefficient (a b c)^2. The signs are those of Eq. (54), included once. Applying the LPO maps to the entire Bell operator before tensoring is a different functional.", DescribeRole.Definition),
            Node("table_bound", "The universal context-table bound", "Assume four finite nonnegative probability tables of mass one, bounded outputs, and singleton expectations agreeing at repeated setting labels. The squared-weight termwise witness is at most two. No pair of settings repeats across these four contexts, and no additional constraints on pair moments are needed. Independently draw a triple from each table; for every setting multiply the two outcomes in its incident contexts, then multiply by that setting's mean. The resulting six responses lie in [-1,1]. Every selected triple expectation factors into its original triple moment times the square of its three single means. Averaging the classical Mermin inequality proves the bound. The Lean statement is this finite-table result; the quantum consequence follows by the product-effect construction described below.", DescribeRole.Theorem),
            Node("table_abs_bound", "The absolute bound", "The same hypotheses give absolute witness at most two. Negating the first output in all contexts and the two Alice means negates every triple moment, while preserving squared weights, and gives the lower bound.", DescribeRole.Theorem),
            Node("odd", "The retained odd moments", "The four components are a+b+c+t, a+b-c-t, a-b+c-t, a-b-c+t. They are the odd parts of the eight positivity rows paired under simultaneous outcome reversal.", DescribeRole.Definition),
            Node("even", "The three omitted pair moments", "For pair moments d,e,f, the four components are 1+d+e+f, 1+d-e-f, 1-d+e-f, 1-d-e+f. Their sum is four.", DescribeRole.Definition),
            Node("positiveRows", "Eight positivity rows", "For each of the four paired rows, both even(i)+odd(i) and even(i)-odd(i) are nonnegative. Dividing these eight numbers by eight gives a probability table.", DescribeRole.Definition),
            Node("eliminate_pairs", "Exact elimination of pair moments", "There exist d,e,f satisfying all eight positivity rows if and only if the sum of the absolute values of the four odd components is at most four. Necessity follows from abs(odd(i)) <= even(i). For sufficiency set H(i)=abs(odd(i))+(4-sum abs(odd))/4, so sum H=4, and recover d,e,f by the inverse Hadamard formulas. This is exact existential elimination, not a constraint obtained by setting the omitted pair moments to zero.", DescribeRole.Theorem),
            Paragraph(Text("For a finite-dimensional density matrix and local Hermitian contractions, the positive product effects (I+alpha A)/2 tensor (I+beta B)/2 tensor (I+gamma C)/2 have nonnegative expectations, sum to one, and give shared single means. The finite-table theorem therefore proves the unrestricted quantum consequence in any finite dimension, including three qubits and binary POVMs. The matrix-to-table construction is an elementary written consequence, not a separately compiled matrix theorem in this module. The value two is attained by |000><000| with both Alice settings -Z and all Bob/Charlie settings Z; this matrix calculation is written, and its scalar arithmetic is replayed separately. The C3322 bound four is outside this result.")))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("local-perception-mermin-" + (name == "positiveRows" ? "positive-rows" : name.Replace('_','-'))),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(Presentation(name))), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Sub(string s, Formula i) => Seq(X(s), Underscore, Grp(i));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(X(s), [.. xs]);
    private static Formula L(Formula i) => Sub("L", i);
    private static Formula Hh(Formula i) => Sub("h", i);
    private static Formula Score() => Call("S", X("m"), X("t"));
    private static Formula Term(byte a, byte b, byte c, byte v) =>
        Seq(Par(Seq(Sub("m", D(a)), Sub("m", D(b)), Sub("m", D(c)))), Caret, Grp(D(2)), Sub("t", D(v)));
    private static Formula Presentation(string name) => name switch
    {
        "avg" => Seq(Call("avg", X("p"), X("f")), Eq, Sum, Underscore, Grp(X("i")), Sub("p", X("i")), Sub("f", X("i"))),
        "avg4" => Seq(Call("avgfour", X("p"), X("q"), X("r"), X("s"), X("f")), Eq,
            Sum, Underscore, Grp(Seq(X("i"), Comma, X("j"), Comma, X("k"), Comma, X("l"))),
            Sub("p", X("i")), Sub("q", X("j")), Sub("r", X("k")), Sub("s", X("l")), Call("f", X("i"), X("j"), X("k"), X("l"))),
        "classical_bound" => Seq(X("a"), X("b"), X("c"), Minus, X("a"), X("B"), X("C"), Minus,
            X("A"), X("b"), X("C"), Minus, X("A"), X("B"), X("c"), Leq, D(2)),
        "edge" => Seq(X("e"), Eq, Par(Seq(Par(Seq(D(0), Comma, D(2), Comma, D(4))), Comma,
            Par(Seq(D(0), Comma, D(3), Comma, D(5))), Comma,
            Par(Seq(D(1), Comma, D(2), Comma, D(5))), Comma, Par(Seq(D(1), Comma, D(3), Comma, D(4)))))),
        "triple" => Seq(Sub("t", X("v")), Eq, Sum, Underscore, Grp(X("i")),
            Call("p", X("v"), X("i")), Prod, Underscore, Grp(Seq(X("j"), Eq, D(0))), Caret, Grp(D(2)),
            Call("u", X("v"), X("j"), X("i"))),
        "witness" => Seq(Score(), Eq, Term(0,2,4,0), Minus, Term(0,3,5,1), Minus, Term(1,2,5,2), Minus, Term(1,3,4,3)),
        "table_bound" => Seq(Score(), Leq, D(2)),
        "table_abs_bound" => Seq(Bar, Score(), Bar, Leq, D(2)),
        "odd" => Seq(X("L"), Eq, Par(Seq(
            X("a"), Plus, X("b"), Plus, X("c"), Plus, X("t"), Comma,
            X("a"), Plus, X("b"), Minus, X("c"), Minus, X("t"), Comma,
            X("a"), Minus, X("b"), Plus, X("c"), Minus, X("t"), Comma,
            X("a"), Minus, X("b"), Minus, X("c"), Plus, X("t")))),
        "even" => Seq(X("h"), Eq, Par(Seq(
            D(1), Plus, X("d"), Plus, X("e"), Plus, X("f"), Comma,
            D(1), Plus, X("d"), Minus, X("e"), Minus, X("f"), Comma,
            D(1), Minus, X("d"), Plus, X("e"), Minus, X("f"), Comma,
            D(1), Minus, X("d"), Minus, X("e"), Plus, X("f")))),
        "positiveRows" => Seq(Forall, Sp, X("i"), Colon, Hh(X("i")), Plus, L(X("i")), Geq, D(0), Land, Sp,
            Hh(X("i")), Minus, L(X("i")), Geq, D(0)),
        "eliminate_pairs" => Seq(Par(Seq(Exists, Sp, X("d"), Comma, X("e"), Comma, X("f"), Colon,
            Call("positiveRows", X("a"), X("b"), X("c"), X("t"), X("d"), X("e"), X("f")))),
            Iff, Sum, Underscore, Grp(Seq(X("i"), Eq, D(0))), Caret, Grp(D(3)), Bar, L(X("i")), Bar, Leq, D(4)),
        _ => throw new System.ArgumentException("Unknown presentation")
    };

}
