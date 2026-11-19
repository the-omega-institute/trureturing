using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229632StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229632";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229632: exact defect recurrence"),
        Blocks(Paragraph(Text("The literal array has n rows, 3 columns and exactly 2 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 9 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. The active leading sector, initial vector and cached prefix are a block extension of HardinA229529Strip. Its original certificate supplies the inherited active successor and initial projections. Only the appended sectors and rows are stored here.")),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229632Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("3"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229581Strip.horizontal"), Call("HardinA229529Strip.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("3")), App(V("A"), Pair(V("i"), V("j"))))))), Num("2")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("3"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("3"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("3")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("3")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("8")))), Sub(Add(Sub(Add(Sub(Mul(Num("15"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("7"))))), Mul(Num("81"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("6")))))), Mul(Num("185"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("5")))))), Mul(Num("162"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("4")))))), Mul(Num("60"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("3")))))), Mul(Num("8"), AsInt(Call("HardinA229632Strip.a", Add(V("n"), Num("2")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The recurrence holds at every index at least 8. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229632"), ResolutionKind.Proved)))));

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

    private static Formula AsInt(Formula value) => Parenthesized(Seq(value, Colon, Sp, Call("Int")));

}
