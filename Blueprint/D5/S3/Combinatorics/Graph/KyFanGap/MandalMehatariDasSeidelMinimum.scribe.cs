using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class MandalMehatariDasSeidelMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mandalmehataridas2022seidelchain");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected chain graph has at least the Seidel energy of each member of Gamma(n,k), with equality precisely for the members of that family.",
        H("Minimum Seidel energy of chain graphs"), Blocks(
            Node("energy", "Characteristic-root energy", "energy", EnergyDefinition(), DescribeRole.Definition,
                "Page 2: \"The Seidel energy SE(G) of a graph G is defined as the sum of absolute values of the eigenvalues of Seidel matrix S.\" The expression uses real characteristic roots with multiplicity. Its applications here are real symmetric matrices.", true),
            Node("energy-eigenvalues", "Energy in an eigenbasis", "energy_eigenvalues", EigenvalueIdentity(false), DescribeRole.Theorem,
                "For a real symmetric matrix, the real roots of the characteristic polynomial are precisely its eigenvalues with multiplicity."),
            Node("absolute-square-root", "Trace of the positive square root", "Spectral.sum_abs_eq_trace_sqrt", EigenvalueIdentity(true), DescribeRole.Theorem,
                "The positive square root of the transpose product has absolute eigenvalues. Its trace is their sum."),
            Node("binary", "The alternating binary string", "binaryString", BinaryDefinition(), DescribeRole.Definition, BinaryProse, true),
            Node("graph", "The chain graph of a binary string", "chainGraph", GraphDefinition(), DescribeRole.Definition, GraphProse, true),
            Node("seidel", "The Seidel matrix", "seidel", SeidelDefinition(), DescribeRole.Definition,
                "Here A is SimpleGraph.adjMatrix over the real numbers. The expression retains the all-ones matrix, identity matrix, and scalar multiple separately.", true),
            Node("gamma", "The comparison family", "Gamma", GammaDefinition(), DescribeRole.Definition, GammaProse, true),
            Node("claim", "Conjecture 4.14", "claim", Eqn(Call("claim"), Parenthesized(ClaimBody())), DescribeRole.Definition, ClaimProse, true),
            Node("result", "Minimum energy and every equality case", "result", ClaimBody(), DescribeRole.Theorem,
                "Sign switching merges the first 0-run with the final 1-run. Compression gives a real symmetric odd core with weights at least one and first weight greater than one. Its trace-norm minimum and the constant inertia correction give the energy comparison. Equality forces every intermediate run to have length one, exactly the family Gamma. When k=1, switching a bipartition gives the all-ones matrix minus the identity for every graph in the comparison.", resolution: new OpenProblemResolutionClaim(ProblemSlugRef.Create("mmd2205-seidelchain"), ResolutionKind.Proved)))));
    private const string BinaryProse = "The indices are Fin k; false is 0 and true is 1. List.ofFn orders the runs and List.flatten concatenates them.";
    private const string GraphProse = "Page 2, verbatim: \"adding an isolated vertex.\" \"adding a vertex dominating to all previously added isolated vertices only.\" An earlier false position and a later true position are adjacent. The formula gives the entire adjacency relation, including its symmetric case and the absence of loops.";
    private const string GammaProse = "The middle word is k-1 copies of [true,false], representing the 2k-2 singleton runs under the source's underbrace. Natural subtraction is truncated; every parameter is a natural number.";
    private const string ClaimProse = "The functions s,t have domain Fin k and positive natural values; n is their total. Every comparison binary string h in Gamma n k is quantified separately. The energy is the shared characteristic-root energy of the real Seidel matrix.";
    private static DocumentBlock Node(string id, string title, string name, Formula formula, DescribeRole role, string prose, bool literature = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mmd-minimum-" + id), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title),
            StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            SourceProse(id, prose), role, resolution);
    private static Formula SourceSub(string s, Formula i) => new Formula.Subscript(Id(s), i);
    private static Formula SourceRuns() => Seq(
        new Formula.Power(D(0), SourceSub("s", D(1))), Sp,
        new Formula.Power(D(1), SourceSub("t", D(1))), Sp,
        new Formula.Power(D(0), SourceSub("s", D(2))), Sp,
        Dot, Dot, Dot, Sp,
        new Formula.Power(D(0), SourceSub("s", Id("k"))), Sp,
        new Formula.Power(D(1), SourceSub("t", Id("k"))));
    private static Formula SourceGamma() => new Formula.Subscript(Gamma, Seq(Id("n"), Comma, Id("k")));
    private static Formula SourceTotal() => Eqn(Seq(
        Seq(Sum, Underscore, Grp(Seq(Id("i"), Sp, Eq, Sp, D(1))), Caret, Grp(Id("k"))), Sp,
        Parenthesized(Add(SourceSub("s", Id("i")), SourceSub("t", Id("i"))))), Id("n"));
    private static Formula SourceIndexRange() => Parenthesized(Seq(D(1), Leq, Sp, Id("i"), Leq, Sp, Id("k")));
    private static BlockSequence SourceProse(string id, string prose)
    {
        if (id == "seidel") return Blocks(Paragraph(
            Text("Page 2, verbatim: Let "), Math(Id("G")), Text(" be a simple, connected, finite graph with vertex set "),
            Math(Eqn(Id("V"), Seq(OpenBrace, SourceSub("v",D(1)),Comma,SourceSub("v",D(2)),Comma,Dot,Dot,Dot,Comma,SourceSub("v",Id("n")),CloseBrace))),
            Text(". Let "), Math(Id("A")), Text(" be the (0,1)-adjacency matrix [12, 17] of "), Math(Id("G")),
            Text(". Then the Seidel matrix [1, 2, 6, 9, 19, 20, 22, 23, 25] is a square matrix of order "), Math(Id("n")), Text(" defined by "),
            Math(Eqn(Id("S"), Sub(Sub(Id("J"),Id("I")), Mul(D(2),Id("A"))))),
            Text(", where "), Math(Id("J")), Text(" is all "), Math(D(1)), Text(" matrix and "), Math(Id("I")), Text(" is the identity matrix.")),
            Paragraph(Text(prose)));
        if (id == "claim") return Blocks(Paragraph(
            Text("Conjecture 4.14, page 25, verbatim: Let "), Math(Id("G")),
            Text(" be a chain graph of order "), Math(Id("n")), Text(" with the binary string "),
            Math(Eqn(Id("b"), SourceRuns())), Text(" such that "),
            Math(Seq(SourceTotal(), Comma, Sp, SourceSub("s", Id("i")), Geq, Sp, D(1), Sp, SourceIndexRange())),
            Text(", and "), Math(Seq(SourceSub("t", Id("i")), Geq, Sp, D(1), Sp, SourceIndexRange())),
            Text(". Then "), Math(Seq(Call("SE", Id("G")), Geq, Sp, Call("SE", Id("H")))),
            Text(", where "), Math(Seq(Id("H"), InMacro, Sp, SourceGamma())),
            Text(". Moreover, the equality holds if and only if "), Math(Seq(Id("G"), InMacro, Sp, SourceGamma())), Text(".")),
            Paragraph(Text(prose)));
        if (id == "binary") return Blocks(Paragraph(
            Text("Page 2, verbatim: We represent a chain graph "), Math(Id("G")), Text(" on "), Math(Id("n")),
            Text(" vertices using a binary string "),
            Math(Eqn(Id("b"), Seq(new Formula.Subscript(Alpha,D(1)), new Formula.Subscript(Alpha,D(2)), new Formula.Subscript(Alpha,D(3)), Sp, Dot,Dot,Dot,Sp,new Formula.Subscript(Alpha,Id("n"))))),
            Text(" of length "), Math(Id("n")), Text(", where "), Math(Eqn(new Formula.Subscript(Alpha,Id("i")),D(0))),
            Text(" if the vertex "), Math(SourceSub("v",Id("i"))), Text(" is added as an isolated vertex, and "),
            Math(Eqn(new Formula.Subscript(Alpha,Id("i")),D(1))), Text(" if the vertex "), Math(SourceSub("v",Id("i"))),
            Text(" is dominating to all the previously added isolated vertices. As we start from a single vertex we always take "),
            Math(Eqn(new Formula.Subscript(Alpha,D(1)),D(0))),
            Text(", and since we are considering connected graphs only so "), Math(Eqn(new Formula.Subscript(Alpha,Id("n")),D(1))),
            Text(". For any "),Math(Id("n")),Text(" vertex chain graph, without loss of generality, we represent it by the binary string "),
            Math(Eqn(Id("b"),SourceRuns())), Text(", where "),
            Math(Seq(SourceSub("s",Id("i")),Comma,Sp,SourceSub("t",Id("i")),Geq,Sp,D(1))), Text(" and "),Math(SourceTotal()),
            Text(". A chain graph is a bipartite graph, and it is complete bipartite if and only if "),Math(Eqn(Id("k"),D(1))),Text(".")),
            Paragraph(Text(prose)));
        if (id == "gamma") return Blocks(Paragraph(
            Text("Page 21: Let "),Math(SourceGamma()),Text(" be a class of chain graphs of order "),Math(Id("n")),
            Text(" with the binary string "),Math(Seq(Id("b"),Eq,Sp,new Formula.Power(D(0),SourceSub("s",D(1))),Sp,
                new Formula.Power(D(1),D(1)),Sp,new Formula.Power(D(0),D(1)),Sp,new Formula.Power(D(1),D(1)),Sp,new Formula.Power(D(0),D(1)),Dot,Dot,Dot,Sp,new Formula.Power(D(0),D(1)),Sp,new Formula.Power(D(1),SourceSub("t",Id("k"))))),
            Text(" such that "),Math(Eqn(Add(SourceSub("s",D(1)),SourceSub("t",Id("k"))),Add(Sub(Id("n"),Mul(D(2),Id("k"))),D(2)))),
            Text(" with "),Math(Seq(D(1),Leq,Sp,SourceSub("s",D(1)),Leq,Sp,Add(Sub(Id("n"),Mul(D(2),Id("k"))),D(1)))),
            Text(" and "),Math(Seq(D(1),Leq,Sp,SourceSub("t",Id("k")),Leq,Sp,Add(Sub(Id("n"),Mul(D(2),Id("k"))),D(1)))),Text(".")),
            Paragraph(Text(prose)));
        return Blocks(Paragraph(Text(prose)));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((x, i) => i == 0 ? new[] { Id(x) } : new[] { Dot, Id(x) }).ToArray());
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Seq(Operatorname, Grp(Qualified(s))) : new Formula.Apply(Seq(Operatorname, Grp(Qualified(s))), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(Id(s), Sp, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists, Sp, Parenthesized(Seq(Id(s), Sp, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Lam(string s, Formula t, Formula b) => Seq(Call("fun"), Sp, Parenthesized(Seq(Id(s), Sp, Colon, Sp, t)), Sp, Mapsto, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator o, Formula b) => new Formula.Logic(Parenthesized(a), o, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula ListBool() => Call("List", Call("Bool"));
    private static Formula Append(Formula a, Formula b) => Call("List.append", a, b);
    private static Formula Rep(Formula n, bool bit) => Call("List.replicate", n, Call(bit ? "Bool.true" : "Bool.false"));
    private static Formula Binary(Formula s, Formula t) => Call("binaryString", s, t);
    private static Formula Graph(Formula b) => Call("chainGraph", b);
    private static Formula Seidel(Formula g) => Call("seidel", g);
    private static Formula Energy(Formula a) => Call("energy", a);
    private static Formula GammaF(Formula n, Formula k, Formula b) => Call("Gamma", n, k, b);
    private static Formula Middle(Formula k) => Call("List.flatten", Call("List.replicate", Sub(k, D(1)), Seq(OpenBracket, Call("Bool.true"), Comma, Sp, Call("Bool.false"), CloseBracket)));
    private static Formula BinaryDefinition()
    {
        var k = Id("k"); var s = Id("s"); var t = Id("t"); var i = Id("i");
        var body = Call("List.flatten", Call("List.ofFn", Lam("i", Fin(k), Append(Rep(App(Id("s"), i), false), Rep(App(Id("t"), i), true)))));
        return All("k", Nat(), All("s", Arr(Fin(k), Nat()), All("t", Arr(Fin(k), Nat()), Eqn(Binary(s, t), body))));
    }
    private static Formula GraphDefinition()
    {
        var b = Id("b"); var i = Id("i"); var j = Id("j");
        Formula Edge(Formula u, Formula v) => And(Less(u, v), And(Eqn(Call("List.get", b, u), Call("Bool.false")), Eqn(Call("List.get", b, v), Call("Bool.true"))));
        var index = Fin(Call("List.length", b));
        return All("b", ListBool(), All("i", index, All("j", index,
            Logic(Call("SimpleGraph.Adj", Graph(b), i, j), FormulaLogicOperator.Iff, Logic(Edge(i, j), FormulaLogicOperator.Or, Edge(j, i))))));
    }
    private static Formula SeidelDefinition()
    {
        var n = Id("n"); var g = Id("G");
        var ones = Call("Matrix.of", Call("Function.const", Fin(n), Call("Function.const", Fin(n), Seq(D(1), Sp, Colon, Sp, Real()))));
        return All("n", Nat(), All("G", Call("SimpleGraph", Fin(n)), Eqn(Seidel(g), Sub(Sub(ones, D(1)), Call("HSMul.hSMul", Seq(D(2), Sp, Colon, Sp, Real()), Call("SimpleGraph.adjMatrix", g, Real()))))));
    }
    private static Formula GammaDefinition()
    {
        var n = Id("n"); var k = Id("k"); var b = Id("b"); var s = Id("s"); var t = Id("t");
        var bound = Add(Sub(n, Mul(D(2), k)), D(1));
        var rhs = Ex("s", Nat(), Ex("t", Nat(), And(LeqF(D(1), s), And(LeqF(s, bound), And(LeqF(D(1), t), And(LeqF(t, bound),
            And(Eqn(Add(s, t), Add(Sub(n, Mul(D(2), k)), D(2))), Eqn(b, Append(Append(Rep(s, false), Middle(k)), Rep(t, true))))))))));
        return All("n", Nat(), All("k", Nat(), All("b", ListBool(), Eqn(GammaF(n, k, b), Parenthesized(rhs)))));
    }
    private static Formula ClaimBody()
    {
        var n = Id("n"); var k = Id("k"); var s = Id("s"); var t = Id("t"); var h = Id("h");
        var graphEnergy = Energy(Seidel(Graph(Binary(s, t)))); var comparison = Energy(Seidel(Graph(h)));
        var conclusion = And(LeqF(comparison, graphEnergy), Logic(Eqn(graphEnergy, comparison), FormulaLogicOperator.Iff, GammaF(n, k, Binary(s, t))));
        var sum = Call("Finset.sum", Call("Finset.univ"), Lam("i", Fin(k), Add(App(Id("s"), Id("i")), App(Id("t"), Id("i")))));
        return All("n", Nat(), All("k", Nat(), Imp(LeqF(D(1), k), Imp(LeqF(Mul(D(2), k), n),
            All("s", Arr(Fin(k), Nat()), All("t", Arr(Fin(k), Nat()),
                Imp(All("i", Fin(k), LeqF(D(1), App(Id("s"), Id("i")))), Imp(All("i", Fin(k), LeqF(D(1), App(Id("t"), Id("i")))),
                    Imp(Eqn(sum, n), All("h", ListBool(), Imp(GammaF(n, k, h), conclusion)))))))))));
    }
    private static Formula EnergyDefinition()
    {
        var roots = Call("Polynomial.roots", Call("Matrix.charpoly", Id("M")));
        var absoluteRoots = Call("Multiset.map", Lam("x", Real(), Abs(Id("x"))), roots);
        return Carrier(All("M", Matrix(Id("V")), Eqn(Call("energy", Id("M")), Call("Multiset.sum", absoluteRoots))));
    }
    private static Formula EigenvalueIdentity(bool squareRoot)
    {
        var x = Id("X"); var h = Id("hX");
        var sum = SumOver("i", Id("V"), Abs(Call("Matrix.IsHermitian.eigenvalues", h, Id("i"))));
        return Carrier(All("X", Matrix(Id("V")), All("hX", Call("Matrix.IsHermitian", x), squareRoot
            ? Eqn(sum, Call("Matrix.trace", Call("CFC.sqrt", Mul(Call("Matrix.transpose", x), x))))
            : Eqn(Call("energy", x), sum))));
    }
    private static Formula Matrix(Formula v) => Call("Matrix", v, v, Real());
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert);
    private static Formula SumOver(string s, Formula t, Formula b) => Call("Finset.sum", Call("Finset.univ"), Lam(s, t, b));
    private static Formula Carrier(Formula b) => All("V", Id("Type"),
        Seq(OpenBracket, Call("Fintype", Id("V")), CloseBracket, Sp, OpenBracket, Call("DecidableEq", Id("V")), CloseBracket, Sp, b));
}
