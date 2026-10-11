using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeHistoryCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeHistoryCells", H("NativeHistoryCells"), Blocks(
            Entry("Patterns", "Finite old-class pattern tuples", "Each actually appearing old class chooses one finite depth-d pattern. The tuple type has a finite enumeration. Repeated occurrences of one class share its entire pattern and variable family.", DescribeRole.Definition),
            Entry("Variables", "Class and reached-position variable names", "The dependent sum records the old class and exactly its reached frontier position. Equal ground values are allowed at different names; old class values alone must satisfy the full legal inequality relation.", DescribeRole.Definition),
            Entry("wholeTerm", "Symbolic entire retained row", "Expand every occurrence of an old class with the same class-indexed pattern term. Concrete exterior leaves remain literal and original absent-cut guards cannot be removed.", DescribeRole.Definition),
            Entry("requiredDepth", "Native source-defined observation depth", "The depth is exactly one plus the maximum of zero, all new-cut address lengths and all historical physical-address lengths. Epochs and hidden source size do not enter it.", DescribeRole.Definition),
            Entry("valuesEquiv", "Tuple decomposition inverse", "The explicit splitValues map decomposes every old class through depthEquiv; rawValues reconstructs every class by filling. Both directions are inverse, including empty class and variable types.", DescribeRole.Definition),
            Entry("testHistory", "Source-free invariant history test", "Evaluate the complete finite mixed-epoch history on the fixed all-alpha filling of the finite whole term. This is a symbolic test only and does not assert that its filling is a legal or acquired source.", DescribeRole.Definition),
            Entry("feasiblePatterns", "Finite complete feasibility enumeration", "Enumerate all old-class pattern tuples and retain those passing the invariant history test and every syntactic old disequality. Each cell contains its entire legal valuation fiber without size bounds or representative restriction; ground cells may be singleton.", DescribeRole.Definition),
            Entry("cell_feasibility_exact", "Exact nonempty entire cell test", "The Boolean test passes exactly when some whole valuation satisfies all old-class inequalities and every historical reply. Simultaneous finite ground separation supplies the sufficiency proof. Contradictory histories are total preprocessing inputs, without a service nonemptiness premise.", DescribeRole.Theorem),
            Entry("historyCellEquiv", "Exact native whole-fiber coproduct", "SLH.74.8 is an explicit equivalence from the coproduct of all feasible entire legal filling fibers to every actual original source with the retained canonical old row and complete history. Each cell valuation domain imposes only all old inequalities; the finite feasible-pattern test already guarantees history for every filling. cellSource reconstructs the original; sourceCell recovers every class and its unique pattern/frontier subtrees. No U2-U8 conclusion is assumed.", DescribeRole.Definition),
            Entry("recutCell", "Whole-cell exact new-row interface", "At requiredDepth Q H, apply fieldwise symbolic recutting to wholeTerm using both its proved residual-depth guard and the derived Q length bound; neither guard is passed as a caller assumption. The output includes the actual independent record, reached order and actual new subtrees. canonicalRow_record_iff relates that record to the actual canonical Q row. This U1 interface is not the full finite-budget Theorem74.4: unification completeness, serial operational replay, decoding, certificate budgets, GB and the four equivalence directions remain separate obligations.", DescribeRole.Definition)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativehistorycells-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n switch
    {
        "cell_feasibility_exact" => StatementSource.FromAuthor(Disp(All("C", V("LiteralRow"), All("d", V("Nat"), All("eta", Call("Patterns", V("C"), V("d")), All("H", V("History"), Imp(All("e", Call("Prod", V("Nat"), Call("Prod", V("Address"), V("Reply"))), Imp(Mem(V("e"), V("H")), Less(Call("length", Call("fst", Call("snd", V("e")))), V("d")))), IffOf(EqOf(Call("feasible", V("eta"), V("H")), V("true")), Some("v", Arr(Call("Variables", V("eta")), V("Source")), Call("LegalFilling", V("eta"), V("H"), V("v"))))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
