using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;
internal sealed class FibonacciGrayPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FibonacciGrayPath", H("FibonacciGrayPath"), Blocks(
            Paragraph(Text("The binary word at dimension d is a function from Fin d to Bool. Adm means that no two consecutive coordinates are true, including the empty word at dimension zero. The reflected list starts with the empty word at dimension zero and with zero and one at dimension one. At dimension d plus two it concatenates zero prefixed to the reversed list at dimension d plus one with ten prefixed to the reversed list at dimension d.")),
            Paragraph(Text("The two blocks have different first bits. The existing admissible splitting equivalence proves completeness, and prefix injectivity proves that every word occurs exactly once. Reversal retains one-bit adjacency inside each block. The head of the list at dimension d plus one is zero prefixed to the last word at dimension d; this identifies the joining words as zero-zero-u and one-zero-u, which differ at their first coordinate.")),
            Paragraph(Text("This is the classical Fibonacci-cube spanning path of Klavzar, Structure of Fibonacci cubes: a survey, Proposition 3.1, author manuscript pages 5-6, DOI 10.1007/s10878-011-9433-z. The survey attributes the construction to Cong, Zheng and Sharma. Only a path is used; no Hamilton cycle or prescribed endpoint is asserted. The existing admissibleWord_card_eq_fib theorem supplies the capacity and is applied through the bijection between list indices and admissible words.")),
            Describe.Lean(DescribeId.Create("gray"),
                DeclarationHandle.Create("D5/S1/Words/AdmissibleWords/FibonacciGrayPath.gray"),
                H("The reflected list of admissible words"), StatementSource.FromAuthor(Disp(GrayDefinition())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/klavzar2013structure")),
                Blocks(Paragraph(Text("The list has the dependent type List (Fin d to Bool). The empty word forms the list at zero, and the two constant one-bit words form the list at one. The recursion reverses both smaller lists before prefixing false and true-false, respectively, and concatenates the resulting lists."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hamming-cons"),
                DeclarationHandle.Create("D5/S1/Words/AdmissibleWords/FibonacciGrayPath.hamming_cons"),
                H("Hamming distance after prefixing"), StatementSource.FromAuthor(Disp(HammingConsStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Prefixing two binary words adds one to their Hamming distance exactly when the two prefix bits differ."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("stage-path"),
                DeclarationHandle.Create("D5/S1/Words/AdmissibleWords/FibonacciGrayPath.StagePath"),
                H("A finite path of admissible words"), StatementSource.FromAuthor(Disp(StagePathDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The record specifies h plus one admissible words of dimension d, injectivity of the word map, and Hamming distance one between each pair of consecutive indices. Fin.castSucc and Fin.succ embed an edge index into its two endpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-stage-path"),
                DeclarationHandle.Create("D5/S1/Words/AdmissibleWords/FibonacciGrayPath.exists_stage_path"),
                H("Distinct one-bit stages"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/klavzar2013structure")),
                Blocks(Paragraph(Text("The first h plus one words of the spanning list form the immutable stage path. Capacity alone is not an edge premise: the reflected-list argument establishes every consecutive edge. Dimension zero permits h equal to zero and supplies its unique stage. The h positive edges are indexed by Fin h; castSucc and succ are the two adjacent indices in Fin (h plus one)."))), DescribeRole.Theorem))));

    private static Formula GrayDefinition() {
        var d = V("d"); var w = V("w");
        var dependentType = Seq(Par(Seq(d, Colon, Sp, V("Nat"))), Sp, To, Sp,
            Call("List", Arr(Call("Fin", d), V("Bool"))));
        var empty = Seq(OpenBracket, Qualified("Fin", "elim0"), CloseBracket);
        var constantFalse = Par(Seq(LambdaLower, Sp, V("i"), Sp, Mapsto, Sp, V("false")));
        var constantTrue = Par(Seq(LambdaLower, Sp, V("i"), Sp, Mapsto, Sp, V("true")));
        var singletonBits = Seq(OpenBracket, constantFalse, Comma, Sp, constantTrue, CloseBracket);
        var left = Apply(Qualified("List", "map"),
            Par(Apply(Qualified("Fin", "cons"), V("false"))),
            Par(Apply(Qualified("List", "reverse"), Par(Call("gray", Par(Add(d, D(1))))))));
        var prefix = Par(Seq(LambdaLower, Sp, w, Sp, Mapsto, Sp,
            Apply(Qualified("Fin", "cons"), V("true"),
                Par(Apply(Qualified("Fin", "cons"), V("false"), w)))));
        var right = Apply(Qualified("List", "map"), prefix,
            Par(Apply(Qualified("List", "reverse"), Par(Call("gray", d)))));
        var recursion = All("d", V("Nat"), Eq(Call("gray", Par(Add(d, D(2)))),
            Seq(Par(left), Sp, Plus, Plus, Sp, Par(right))));
        return new Formula.Aligned([
            Seq(V("gray"), Colon, Sp, Par(dependentType)),
            Eq(Call("gray", D(0)), empty),
            Eq(Call("gray", D(1)), singletonBits),
            recursion]);
    }

    private static Formula StagePathDefinition() {
        var d = V("d"); var h = V("h"); var word = V("word"); var i = V("i");
        var index = Call("Fin", Par(Add(h, D(1))));
        var wordType = Arr(index, Arr(Call("Fin", d), V("Bool")));
        var admissible = All("i", index, Call("Adm", d, Apply(word, i)));
        var injective = Apply(Qualified("Function", "Injective"), word);
        var consecutive = All("i", Call("Fin", h), Eq(Call("hammingDist",
            Apply(word, Apply(Qualified("Fin", "castSucc"), i)),
            Apply(word, Apply(Qualified("Fin", "succ"), i))), D(1)));
        var fields = Seq(OpenBrace,
            V("word"), Colon, Sp, wordType, Semi, Quad, Sp,
            V("admissible"), Colon, Sp, admissible, Semi, Quad, Sp,
            V("injective"), Colon, Sp, injective, Semi, Quad, Sp,
            V("consecutive"), Colon, Sp, consecutive, CloseBrace);
        return All("d", V("Nat"), All("h", V("Nat"),
            Seq(Call("StagePath", d, h), Colon, F.Eq, Sp, fields)));
    }

    private static Formula HammingConsStatement() {
        var d = V("d"); var a = V("a"); var b = V("b"); var x = V("x"); var y = V("y");
        var cons = Seq(Operatorname, Grp(V("Fin"), Dot, V("cons")));
        var lhs = Call("hammingDist", new Formula.Apply(cons, [a, x]), new Formula.Apply(cons, [b, y]));
        var indicator = Call("ite", Par(Eq(a, b)), D(0), D(1));
        return All("d", V("Nat"), All("a", V("Bool"), All("b", V("Bool"),
            All("x", Arr(Call("Fin", d), V("Bool")), All("y", Arr(Call("Fin", d), V("Bool")),
                Eq(lhs, Add(Par(indicator), Call("hammingDist", x, y))))))));
    }

    private static Formula Statement() {
        var d=V("d"); var h=V("h"); var w=V("w"); var i=V("i");
        var word=Arr(Call("Fin",Add(h,D(1))),Arr(Call("Fin",d),V("Bool")));
        var result=Ex("w",word,And(
            All("i",Call("Fin",Add(h,D(1))),Call("Adm",d,Call("w",i))),
            Call("Injective",w),
            All("i",Call("Fin",h),Eq(Call("hammingDist",Call("w",Call("castSucc",i)),
                Call("w",Call("succ",i))),D(1)))));
        return All("d",V("Nat"),All("h",V("Nat"),
            Imp(Le(Add(h,D(1)),Call("fib",Add(d,D(2)))),result)));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) {
        var r = xs[^1];
        for (int i = xs.Length-2; i >= 0; --i) r = Seq(Par(xs[i]), Sp, Land, Sp, Par(r));
        return r;
    }
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Ex(string n, Formula t, Formula b) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
