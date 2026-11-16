using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7;
internal sealed class HardinA229585StripOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.")),
            Describe.Lean(DescribeId.Create("nextclasses"),
                DeclarationHandle.Create(Prefix + "nextClasses"), H("Exact successor-class multiset"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Eq(Call("HardinA229585StripOrbit.nextClasses", V("p"), V("d")), SumOver("r", V("Row"), Conditional(Leq(Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), V("d")), Call("Singleton.singleton", Call("HardinA229585StripData.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(V("d"), Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")))))), Num("0")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every permitted row contributes its destination class once; disallowed rows contribute the empty multiset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("images"),
                DeclarationHandle.Create(Prefix + "images"), H("Successor multisets"),
                StatementSource.FromAuthor(Disp(Seq(Call("HardinA229585StripOrbit.images"), Colon, Sp, Arrow(Call("Fin", Num("72")), Call("Multiset", Call("Fin", Num("72"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The table has 72 multisets in cl index order, each containing destination "
                    + "indices in Fin 72 with their successor multiplicities. For source classes below "
                    + "16, the destinations below 16 are generated from HardinA233255Recurrence.table: "
                    + "each j contributes table i j converted to a natural multiplicity via "
                    + "Multiset.replicate, using Fin.castAdd 56 for the inclusion. Only destinations "
                    + "at least 16 are retained as a literal tail. For sources zeroBudgetClass i, "
                    + "the complete multiset is generated from the same owner row through "
                    + "HardinA229585StripData.zeroBudgetClass on the destination index. The other "
                    + "rows retain their finite lists. The OrbitChecks.canonical_next theorems identify images with "
                    + "nextClasses on each valid class interval, and "
                    + "HardinA229585StripOrbitTable.table_counts pins each destination multiplicity to "
                    + "the corresponding entry of T."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-count"),
                DeclarationHandle.Create(Prefix + "sum_count"), H("Histogram as a multiset multiplicity"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), All("s", Call("Fin", Num("72")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), V("d")), Eq(Call("HardinA229585StripData.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(V("d"), Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), Call("Int.ofNat", Call("Multiset.count", V("s"), Call("HardinA229585StripOrbit.nextClasses", V("p"), V("d")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Counting one selected class commutes with the finite sum of singleton contributions."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}
