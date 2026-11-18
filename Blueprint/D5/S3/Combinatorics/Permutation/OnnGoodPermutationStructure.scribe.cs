using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class OnnGoodPermutationStructureDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/onn2023supmodular");
    private const string GoodQuote = "Section 2, page 4: “We say an m×n matrix σ whose entries are a permutation of 1,2,…,mn is good on i,j with 1≤i<m and 1≤j<n if the maximum among σᵢ,ⱼ,σᵢ,ⱼ₊₁,σᵢ₊₁,ⱼ,σᵢ₊₁,ⱼ₊₁ is either σᵢ,ⱼ or σᵢ₊₁,ⱼ₊₁ and the minimum among these entries is either σᵢ,ⱼ₊₁ or σᵢ₊₁,ⱼ.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local extreme positions force a unique split into two chains.", H("The structure of good permutations"),
        Blocks(
            Paragraph(Text("An array is an equivalence (Fin m × Fin n) ≃ Fin (m*n). Coordinates are zero-based; entry adds one to each rank. "
                + "Natural subtraction is truncated. List.Pairwise uses the strict order on natural numbers.")),
            Node("entry", "One-based entries", EntryFormula(),
                "Introduction, page 1: “For an m×n matrix σ whose entries form a permutation of 1,2,…,mn, let A^σ be obtained from A by permuting its entries such that σᵢ,ⱼ<σᵣ,ₛ implies A^σᵢ,ⱼ≤A^σᵣ,ₛ.” "
                + "The equivalence records zero-based ranks; the displayed function adds one and returns zero outside the rectangle.", true, true),
            Node("GoodSquare", "Extreme positions in a square", SquareFormula(), GoodQuote, true, true),
            Node("GoodAt", "Goodness at one adjacent square", AtFormula(), GoodQuote + " The source square (i,j) has coordinates (i−1,j−1) here.", true, true),
            Node("Good", "Goodness at every adjacent square", GoodFormula(), GoodQuote + " Every in-range adjacent square satisfies this condition.", true, true),
            Node("TwoChains", "The two increasing chains", ChainsFormula(),
                "The first chain follows B up to k and returns along T in reverse. The second returns along T from n to k and then follows B. Empty chains are allowed.", true),
            Node("TypeA", "The first three-by-three type", TypeFormula(true),
                "The two increasing lists meet at the center and impose g<d<e<b<a and c<f<e<h<i.", true),
            Node("TypeB", "The second three-by-three type", TypeFormula(false),
                "The two increasing lists meet at the center and impose c<b<e<d<a and g<h<e<f<i.", true),
            Node("Structure", "All rectangular structural cases", StructureFormula(),
                "One-dimensional arrays have no adjacent square. Two-row and two-column arrays have a unique chain split. The only remaining case is three by three, with TypeA or TypeB.", true),
            Node("transpose", "Transposing a rank array", TransposeFormula(),
                "Swap the two coordinates and transport the label through finCongr along m*n=n*m. The local proof h is obtained by natural-number arithmetic.", true),
            Node("good_transpose", "Goodness and transposition", Rect(IffF(Call("Good", Call("transpose", V("s"))), Call("Good", V("s")))),
                "Transposition exchanges the two off-diagonal entries and preserves both extreme-position conditions."),
            Node("two_good_iff", "A unique split in every width", AllN("n", All("s", Array(D(2), V("n")),
                IffF(Call("Good", V("s")), UniqueSplit(V("n"), Row(D(0)), Row(D(1)))))),
                "A negative row sign propagates to every later column. Its first occurrence separates the two increasing chains, and their inequalities make the split unique."),
            Node("three_good_iff", "The four compatible squares", All("s", Array(D(3), D(3)),
                IffF(Call("Good", V("s")), OrF(Call("TypeA", Call("entry", V("s"))), Call("TypeB", Call("entry", V("s")))))),
                "The four local extreme-position conditions give exactly the two three-by-three types."),
            Node("no_good_large", "No three-by-four subrectangle", Rect(Imp(LeF(D(3), V("m")),
                Imp(LeF(D(4), V("n")), Seq(Neg, Call("Good", V("s")))))),
                "Theorem 1.3, page 2: “For m≤n, a universal σ exists if and only if m=1,2 or m=n=3.” "
                + "Overlapping three-by-three blocks force a shared column both to decrease and to be nonmonotone.", false, true),
            Node("good_of_one", "The one-dimensional cases", Rect(Imp(OrF(Equal(V("m"), D(1)), Equal(V("n"), D(1))), Call("Good", V("s")))),
                "There is no adjacent square when either dimension is one."),
            Node("good_iff_structure", "The complete characterization", Rect(Imp(LtF(D(0), V("m")), Imp(LtF(D(0), V("n")),
                IffF(Call("Good", V("s")), Call("Structure", V("s")))))),
                "The unique sign split handles both two-dimensional orientations. Local compatibility gives the three-by-three alternatives; overlapping blocks exclude every larger rectangle."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false, bool literature = false) => Describe.Lean(
        DescribeId.Create("onn-structure-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Root + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula AllN(string name, Formula body) => All(name, Nat, body);
    private static Formula AllRows(Formula body) => All("T", Arrow(Nat, Nat), All("B", Arrow(Nat, Nat), body));
    private static Formula Rect(Formula body) => AllN("m", AllN("n", All("s", Array(V("m"), V("n")), body)));
    private static Formula Array(Formula m, Formula n) => Parenthesized(Seq(Parenthesized(Seq(Call("Fin", m), Times, Call("Fin", n))), Equiv, Call("Fin", Mul(m, n))));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, To, b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula AndF(params Formula[] xs) => Join(FormulaLogicOperator.And, xs);
    private static Formula OrF(params Formula[] xs) => Join(FormulaLogicOperator.Or, xs);
    private static Formula Join(FormulaLogicOperator op, Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--) r = new Formula.Logic(Parenthesized(xs[i]), op, Parenthesized(r));
        return r;
    }
    private static Formula Lam(string name, Formula type, Formula body) => Parenthesized(Seq(Parenthesized(Seq(V(name), Colon, type)), Mapsto, Sp, body));
    private static Formula Tuple(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula FinTerm(Formula value, string proof) => Seq(Langle, Sp, value, Comma, V(proof), Rangle);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Row(Formula i) => Call("entry", V("s"), i);
    private static Formula UniqueSplit(Formula n, Formula t, Formula b) => Seq(Exists, Bang, V("k"), Colon, Nat, Comma, Call("TwoChains", n, t, b, V("k")));
    private static Formula LessRelation => Lam("x", Nat, Lam("y", Nat, LtF(V("x"), V("y"))));
    private static Formula Pairwise(Formula list) => App(Q("List", "Pairwise"), LessRelation, list);
    private static Formula OfFn(Formula width, Formula value) => App(Q("List", "ofFn"), Lam("j", Call("Fin", width), value));
    private static Formula Reverse(Formula list) => App(Q("List", "reverse"), list);
    private static Formula Append(Formula a, Formula b) => App(Q("List", "append"), a, b);
    private static Formula EntryFormula()
    {
        var value = Add(Val(App(V("s"), Tuple(FinTerm(V("i"), "hi"), FinTerm(V("j"), "hj")))), D(1));
        var body = Seq(V("if"), Sp, V("hi"), Colon, LtF(V("i"), V("m")), Sp, V("then"), Sp,
            Parenthesized(Seq(V("if"), Sp, V("hj"), Colon, LtF(V("j"), V("n")), Sp, V("then"), Sp, value, Sp, V("else"), Sp, D(0))),
            Sp, V("else"), Sp, D(0));
        return Rect(AllN("i", AllN("j", Equal(Call("entry", V("s"), V("i"), V("j")), body))));
    }
    private static Formula SquareFormula()
    {
        var max = Call("max", Call("max", V("a"), V("b")), Call("max", V("c"), V("d")));
        var min = Call("min", Call("min", V("a"), V("b")), Call("min", V("c"), V("d")));
        return AllN("a", AllN("b", AllN("c", AllN("d", Equal(Call("GoodSquare", V("a"), V("b"), V("c"), V("d")),
            Parenthesized(AndF(OrF(Equal(max, V("a")), Equal(max, V("d"))), OrF(Equal(min, V("b")), Equal(min, V("c"))))))))));
    }
    private static Formula AtFormula() => Rect(AllN("i", AllN("j", Equal(Call("GoodAt", V("s"), V("i"), V("j")), Parenthesized(
        AndF(LtF(Add(V("i"), D(1)), V("m")), LtF(Add(V("j"), D(1)), V("n")),
            Call("GoodSquare", Call("entry", V("s"), V("i"), V("j")), Call("entry", V("s"), V("i"), Add(V("j"), D(1))),
                Call("entry", V("s"), Add(V("i"), D(1)), V("j")), Call("entry", V("s"), Add(V("i"), D(1)), Add(V("j"), D(1))))))))));
    private static Formula GoodFormula() => Rect(Equal(Call("Good", V("s")), Parenthesized(AllN("i", AllN("j",
        Imp(LtF(Add(V("i"), D(1)), V("m")), Imp(LtF(Add(V("j"), D(1)), V("n")), Call("GoodAt", V("s"), V("i"), V("j")))))))));
    private static Formula ChainsFormula()
    {
        var j = Val(V("j")); var k = V("k"); var n = V("n");
        var first = Append(OfFn(k, App(V("B"), j)), Reverse(OfFn(k, App(V("T"), j))));
        var last = Append(Reverse(OfFn(Sub(n, k), App(V("T"), Add(k, j)))), OfFn(Sub(n, k), App(V("B"), Add(k, j))));
        return AllN("n", AllRows(AllN("k", Equal(Call("TwoChains", n, V("T"), V("B"), k), Parenthesized(AndF(LeF(k, n), Pairwise(first), Pairwise(last)))))));
    }
    private static Formula List(params Formula[] xs)
    {
        var items = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (var i = 0; i < xs.Length; i++) { if (i > 0) items.Add(Comma); items.Add(xs[i]); }
        items.Add(CloseBracket); return Seq([.. items]);
    }
    private static Formula TypeFormula(bool a)
    {
        Formula At(byte i, byte j) => App(V("A"), D(i), D(j));
        var l = a ? List(At(2, 0), At(1, 0), At(1, 1), At(0, 1), At(0, 0)) : List(At(0, 2), At(0, 1), At(1, 1), At(1, 0), At(0, 0));
        var r = a ? List(At(0, 2), At(1, 2), At(1, 1), At(2, 1), At(2, 2)) : List(At(2, 0), At(2, 1), At(1, 1), At(1, 2), At(2, 2));
        return All("A", Arrow(Nat, Arrow(Nat, Nat)), Equal(Call(a ? "TypeA" : "TypeB", V("A")), Parenthesized(AndF(Pairwise(l), Pairwise(r)))));
    }
    private static Formula StructureFormula() => Rect(Equal(Call("Structure", V("s")), Parenthesized(OrF(
        Equal(V("m"), D(1)), Equal(V("n"), D(1)),
        AndF(Equal(V("m"), D(2)), UniqueSplit(V("n"), Row(D(0)), Row(D(1)))),
        AndF(Equal(V("n"), D(2)), UniqueSplit(V("m"), Lam("j", Nat, Call("entry", V("s"), V("j"), D(0))), Lam("j", Nat, Call("entry", V("s"), V("j"), D(1))))),
        AndF(Equal(V("m"), D(3)), Equal(V("n"), D(3)), OrF(Call("TypeA", Call("entry", V("s"))), Call("TypeB", Call("entry", V("s")))))))));
    private static Formula TransposeFormula()
    {
        var swap = App(Q("Equiv", "prodComm"), Call("Fin", V("n")), Call("Fin", V("m")));
        var cast = Call("finCongr", V("h"));
        var body = Seq(V("let"), Sp, V("h"), Colon, Equal(Mul(V("m"), V("n")), Mul(V("n"), V("m"))),
            Sp, Colon, Eq, Sp, V("by"), Sp, V("ring"), Semi, Sp,
            App(Q("Equiv", "trans"), App(Q("Equiv", "trans"), swap, V("s")), cast));
        return Rect(Equal(Call("transpose", V("s")), Parenthesized(body)));
    }
}
