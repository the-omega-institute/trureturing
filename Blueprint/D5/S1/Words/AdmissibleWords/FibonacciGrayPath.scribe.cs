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
            Describe.Lean(DescribeId.Create("exists-stage-path"),
                DeclarationHandle.Create("D5/S1/Words/AdmissibleWords/FibonacciGrayPath.exists_stage_path"),
                H("Distinct one-bit stages"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/klavzar2013structure")),
                Blocks(Paragraph(Text("The first h plus one words of the spanning list form the immutable stage path. Capacity alone is not an edge premise: the reflected-list argument establishes every consecutive edge. Dimension zero permits h equal to zero and supplies its unique stage. The h positive edges are indexed by Fin h; castSucc and succ are the two adjacent indices in Fin (h plus one)."))), DescribeRole.Theorem))));

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
