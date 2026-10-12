using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSymbolicRecuttingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSymbolicRecutting", H("NativeSymbolicRecutting"), Blocks(
            Entry("DeepAt", "Residual depth guard", "Every residual variable occurrence lies at or beyond the fixed original depth. This condition is proved for the whole native cell terms, not passed as a substitute for the source theorem.", DescribeRole.Definition),
            Entry("symbolic_history_constant", "History constancy over every filling", "For histories whose physical addresses are shorter than d, all fillings give the same complete history test at every listed epoch. The fixed testing filling can violate old disequalities; it is used solely for this invariant test.", DescribeRole.Theorem),
            Entry("SymbolicExterior", "New holes separate from residual variables", "New holes carry native addresses, while residual variables remain in a different sum constructor. Filling residuals never fills new holes.", DescribeRole.Definition),
            Entry("symbolicOrdered", "Exact new reached order", "Filter Q by finite symbolic navigation and sort the reached addresses lexicographically. No residual occurrence can be crossed before a tested cut ends.", DescribeRole.Definition),
            Entry("symbolicRecord", "Full symbolic record after filling", "The record includes the concrete filled exterior and all ordered reached pairs satisfying equality of their evaluated symbolic subterms. Nonmembership among reached pairs retains disequality.", DescribeRole.Definition),
            Entry("symbolic_recut_exact", "Exact fieldwise native recutting", "SLH.74.9 preserves reached ordering, the entire concrete exterior, every actual new-hole subtree and the complete finite partition. The result is the independent literalRecord of the actual filled original source. The existing canonicalRow_record_iff then fixes the exact canonical-row equality relation. Empty and root Q remain in scope.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativesymbolicrecutting-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n switch
    {
        "symbolic_history_constant" => StatementSource.FromAuthor(Disp(All("X", V("Type"), All("d", V("Nat"), All("t", Call("Term", V("X")), Imp(Call("DeepAt", V("d"), Call("nil"), V("t")), All("H", V("History"), Imp(All("e", Call("Prod", V("Nat"), Call("Prod", V("Address"), V("Reply"))), Imp(Mem(V("e"), V("H")), Less(Call("length", Call("fst", Call("snd", V("e")))), V("d")))), All("test,v", Arr(V("X"), V("Source")), IffOf(Call("Consistent", V("H"), Call("evaluate", V("test"), V("t"))), Call("Consistent", V("H"), Call("evaluate", V("v"), V("t"))))))))))))),
        "symbolic_recut_exact" => StatementSource.FromAuthor(Disp(All("X", V("Type"), All("d", V("Nat"), All("Q", V("CutSet"), All("t", Call("Term", V("X")), All("v", Arr(V("X"), V("Source")), Imp(And(Call("CutPrefixFree", V("Q")), All("q", V("Address"), Imp(Mem(V("q"), V("Q")), Less(Call("length", V("q")), V("d")))), Call("DeepAt", V("d"), Call("nil"), V("t"))), And(EqOf(Call("orderedHoles", V("Q"), Call("evaluate", V("v"), V("t"))), Call("symbolicOrdered", V("Q"), V("t"))), EqOf(Call("cutExterior", V("Q"), Call("nil"), Call("evaluate", V("v"), V("t"))), Call("exteriorFill", V("v"), Call("symbolicExterior", V("Q"), Call("nil"), V("t")))), All("q", V("Address"), Imp(Mem(V("q"), V("Q")), EqOf(Call("subtree", V("q"), Call("evaluate", V("v"), V("t"))), Call("OptionMap", Call("evaluate", V("v")), Call("termAt", V("q"), V("t")))))), EqOf(Call("literalRecord", V("Q"), Call("evaluate", V("v"), V("t"))), Call("symbolicRecord", V("Q"), V("t"), V("v")))))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
