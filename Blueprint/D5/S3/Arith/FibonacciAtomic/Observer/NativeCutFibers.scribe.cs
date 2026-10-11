using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeCutFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeCutFibers", H("NativeCutFibers"), Blocks(
            Entry("labels", "Actually occurring old classes", "The finite support contains exactly the names retained in the actual old row. No unused Nat coordinates become extra source information.", DescribeRole.Definition),
            Entry("LegalValues", "Complete legal old-class valuations", "One value is reused at every occurrence of an old class. Injectivity on the entire appearing class set preserves every cross-class disequality, including classes outside the new cones.", DescribeRole.Definition),
            Entry("legal_values_row", "Actual old-row reconstruction", "Filling an actual canonical row by any entire legal valuation returns the same canonical row. The independent addressed exterior and full partition record prove the bridge. Every absent public cut retains its concrete original leaf guard.", DescribeRole.Theorem),
            Entry("RowFiber", "Entire actual old-row fiber", "The carrier is every actual original Boolean tree with the specified canonicalRow, without a size bound, sample restriction or product-fiber premise.", DescribeRole.Definition),
            Entry("recover", "Mathematical inverse valuation", "The inverse recovers actual class values from an original source in the fiber. This proof operation is not an accessible source identity or subtree-equality service port.", DescribeRole.Definition),
            Entry("rowFiberEquiv", "Exact old-class/source equivalence", "Evaluation and recovery are mutually inverse and evaluation is injective on legal valuations. The complete actual row, rather than a supplied factorization hypothesis, determines the fiber.", DescribeRole.Definition)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativecutfibers-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n switch
    {
        "legal_values_row" => StatementSource.FromAuthor(Disp(All("P", V("CutSet"), Imp(Call("CutPrefixFree", V("P")), All("u", V("Source"), All("v", Call("LegalValues", Call("canonicalRow", V("P"), V("u"))), EqOf(Call("canonicalRow", V("P"), Call("evaluateRow", Call("extend", Call("canonicalRow", V("P"), V("u")), Call("val", V("v"))), Call("canonicalRow", V("P"), V("u")))), Call("canonicalRow", V("P"), V("u"))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
