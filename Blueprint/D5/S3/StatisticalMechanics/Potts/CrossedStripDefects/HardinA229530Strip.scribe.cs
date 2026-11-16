using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229530StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229530";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229530: exact defect recurrence"),
        Blocks(Paragraph(Text("The literal array has n rows, 4 columns and exactly 1 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 10 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. The frozen four_class_certificate supplies proper transitions through scanner_fibres at saturated Seen flags, an exact budget/class cut and division by sixteen. The remaining defective-source and defect-consuming entries are computed separately.")),
            Describe.Lean(DescribeId.Create("shared-between"), DeclarationHandle.Create(Prefix + "between"),
                H("Shared between"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The exact HDA bonds between consecutive rows, shared with the two-defect extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-Valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Shared Valid"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The one-defect residual-budget domain, reused after subtracting one from the two-defect residual budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("Shared cl"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 10 equality-and-budget classes. The two-defect extension embeds this class index as its active leading sector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-T"), DeclarationHandle.Create(Prefix + "T"),
                H("Shared T"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 10 by 10 exact integer transfer. The two-defect extension uses this matrix as its leading block."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Shared initial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The raw labelled initial vector on Fin 10, shared as the leading initial sector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-W"), DeclarationHandle.Create(Prefix + "W"),
                H("Shared W"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The Fin 7 cached forward prefix on Fin 10, shared by the two-defect extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-finite_certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("Shared finite_certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Exact terminal values, validity preservation, successor and initial counts, cached forward recurrence and polynomial relation. The two-defect extension reuses its active successor and initial projections."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("raw-successors"), DeclarationHandle.Create(Prefix + "raw_successors"),
                H("Proper successor counts from saturated scanner fibres"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("At saturated Seen flags, sixteen times every actual proper three-colour successor count is the corresponding HardinSourceContinuations.M entry. The theorem applies the frozen four_class_certificate through scanner_fibres and preserves all target classes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229530Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("4"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229530Strip.horizontal"), Call("HardinA229530Strip.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("4")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("4"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("4"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("4")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("4")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229530Strip.a", Add(V("n"), Num("6"))), Sub(Add(Sub(Mul(Num("14"), Call("HardinA229530Strip.a", Add(V("n"), Num("5")))), Mul(Num("57"), Call("HardinA229530Strip.a", Add(V("n"), Num("4"))))), Mul(Num("56"), Call("HardinA229530Strip.a", Add(V("n"), Num("3"))))), Mul(Num("16"), Call("HardinA229530Strip.a", Add(V("n"), Num("2"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The recurrence holds at every index at least 6. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

}
