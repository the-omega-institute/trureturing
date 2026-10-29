using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeMaskRowEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native masks recover complete original row exteriors",
        H("Masks, reached sets and original coordinate reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-original-mask-row-elimination"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMaskRowElimination.original_mask_row_elimination"),
            H("Complete exterior descriptors and all original rows have one exact image"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The native mask recursively replaces each encountered cut subtree by alpha, the Boolean leaf true. A concrete exterior instead replaces it by its literal address hole. Filling every address hole by alpha gives exactly the native mask. Cutting that filled mask again at the original cuts restores the complete exterior. Thus equality of masks together with equality of reached sets is equivalent to equality of complete exteriors on the original tree carrier. Concrete leaves and ordered branches outside the cuts are retained without a size bound.")),
                Paragraph(Text("For an arbitrary raw row, maskRowHolds means the following conjunction: cutting the label's filled mask at its cut set gives back its literal exterior; the source mask equals that filled mask; the source reached set equals the set of literal address holes; and the entire actual partition equals the label relation. The first conjunct checks address coherence directly. It is automatic for an exterior cut from any source, and rejects malformed raw labels without an attained-label certificate. The other three conjuncts retain both complete exterior descriptors and every partition bit.")),
                Paragraph(Text("Every row is evaluated on the same original source fill(pat,composition(v,name)). The maskExpression operation changes literal address holes to alpha in the symbolic exterior and retains every uncut frontier variable. The second conjunct identifies evaluation of this native term with the concrete mask of that very original source. Each row cut is prefix-free and every cut address has length strictly less than d. The list may contain both old and new cuts and any additional rows. The source has its actual original prefix pattern and the same named frontiers throughout; the identity naming map retains every original frontier coordinate. Early ground leaves, absent cuts, the root cut, uncut frontiers and repeated names remain in scope.")),
                Paragraph(Text("All reached ordered pairs are retained by the underlying row compiler, including diagonals, both orders, repeated classes and all cross-class and off-task disequalities. An empty reached set has no pairs. A one-hole partition has no distinct pair tests; its ordered diagonal is the reflexive equality, and a raw label denying that equality has empty solution domain. No selected partition projection replaces the complete relation.")),
                Paragraph(Text("The same finite extra equations and disequalities enter the existing full row elimination. The output has an explicitly enumerated free subtype of the original finite presentation, a total substitution theta for every original coordinate, and only substituted disequalities delta. One unrestricted valuation z on that free subtype reconstructs every original coordinate, including unused variables and auxiliaries. Replacing all original coordinates in the pattern term therefore reconstructs the same original source. Interpreted substitution histories, mixed image construction, and all-rank cofinality require further results."))),
            DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Fst(Formula a) => C("fst", a);
    private static Formula Snd(Formula a) => C("snd", a);
    private static Formula Bounded(string x, Formula type, Formula list, Formula body) =>
        All(x, type, Imp(Seq(V(x), Sp, InMacro, Sp, list), body));

    private static Formula Exterior()
    {
        var q = V("Q");
        var u = V("u");
        var w = V("w");
        return All("Q", V("CutSet"), All("u", V("Source"), All("w", V("Source"),
            IffOf(And(
                EqOf(C("nativeMask", q, C("nil"), u), C("nativeMask", q, C("nil"), w)),
                EqOf(C("toFinset", C("reachedHoles", q, C("nil"), u)),
                    C("toFinset", C("reachedHoles", q, C("nil"), w)))),
                EqOf(C("cutExterior", q, C("nil"), u), C("cutExterior", q, C("nil"), w))))));
    }

    private static Formula Extras()
    {
        var pair = C("Prod", C("Term", V("X")), C("Term", V("X")));
        var e = V("e");
        return And(
            Bounded("e", pair, Fst(V("extra")), EqOf(C("evaluate", V("v"), Fst(e)), C("evaluate", V("v"), Snd(e)))),
            Bounded("e", pair, Snd(V("extra")), Seq(C("evaluate", V("v"), Fst(e)), Sp, Neq, Sp, C("evaluate", V("v"), Snd(e)))));
    }

    private static Formula Image()
    {
        var o = V("o");
        var z = V("z");
        var e = V("e");
        var free = C("free", o);
        var reconstructed = All("x", V("X"), EqOf(C("evaluate", z, C("theta", o, V("x"))), C("v", V("x"))));
        var negatives = Bounded("e", C("Prod", C("Term", free), C("Term", free)), C("delta", o),
            Seq(C("evaluate", z, Fst(e)), Sp, Neq, Sp, C("evaluate", z, Snd(e))));
        return Some("o", C("RowOutput", V("X")),
            And(EqOf(C("eliminateRows", V("p"), C("patternTerm", V("pat"), V("name")), V("rs"), V("extra")), C("some", o)),
                Some("z", Arr(free, V("Source")), And(reconstructed, negatives))));
    }

    private static Formula Statement()
    {
        var r = V("r");
        var rs = V("rs");
        var source = C("fill", V("pat"), C("composition", V("v"), V("name")));
        var rows = Bounded("r", V("RawRow"), rs, C("maskRowHolds", r, source));
        var expressions = Bounded("r", V("RawRow"), rs,
            EqOf(C("evaluate", V("v"), C("maskExpression", C("symbolicExterior", Fst(r), C("nil"), C("patternTerm", V("pat"), V("name"))))),
                C("nativeMask", Fst(r), C("nil"), source)));
        var prefix = Bounded("r", V("RawRow"), rs, C("CutPrefixFree", Fst(r)));
        var depth = Bounded("r", V("RawRow"), rs,
            Bounded("q", V("Address"), Fst(r), Seq(C("length", V("q")), Sp, Lt, Sp, V("d"))));
        Formula body = Imp(prefix, Imp(depth,
            And(Exterior(), And(expressions, IffOf(And(rows, Extras()), Image())))));
        body = All("v", Arr(V("X"), V("Source")), body);
        body = All("extra", C("SignedConstraints", V("X")), body);
        body = All("rs", C("List", V("RawRow")), body);
        body = All("name", Arr(C("Frontier", V("pat")), V("X")), body);
        body = All("pat", C("Pattern", V("d")), body);
        body = All("d", V("Nat"), body);
        body = All("p", C("Presentation", V("X")), body);
        return All("X", V("Type"), body);
    }
}
