using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229536StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229536";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229536: exact defect recurrence"),
        Blocks(Paragraph(Text("Exactly 1 monochromatic HDA bonds are allowed. The proper transitions and initial class sizes apply HardinColumnContinuations.column_certificate after the exact bond, budget and class cut and natural-to-integer cast. A transfer letter has 3 cells, swept by columns. Its bond sets are the internal horizontal edges and both diagonals between rows; for the column sweep all horizontal and diagonal edges join successive columns. The 8-state matrix is indexed by remaining budget and equality pattern modulo reflection. Every proper-row diagonal block uses HardinColumnContinuations.Hfull. The finite certificate fixes each entry, initialization, terminal vector and forward polynomial identity.")),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229536Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", Num("3")), Call("Fin", V("n"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229588Strip.horizontal"), BetweenBonds(), Call("List.ofFn", Fn("j", Call("Fin", V("n")), Fn("i", Call("Fin", Num("3")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", Num("3")), Call("Fin", V("n"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", Num("3")), Call("Fin", V("n"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), V("n")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), V("n")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("9")))), Sub(Add(Sub(Sub(Sub(Mul(Num("6"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("8"))))), Mul(Num("1"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("7")))))), Mul(Num("28"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("6")))))), Mul(Num("4"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("5")))))), Mul(Num("16"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("4")))))), Mul(Num("4"), AsInt(Call("HardinA229536Strip.a", Add(V("n"), Num("3")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every natural n, the recurrence holds at index n+9, hence at every index at least 9. The exact-budget transfer uses 8 classes. Its zero-temperature entries call the published owner; finite defect counts, forward iterates and a polynomial relation feed DefectTransfer.lumped_count and forward_shift. The colour-permutation action is free once two colours occur; canonical_pattern_card supplies the factor six. The nonconstant premise is proved in the range used by the recurrence. This is a statement about finite canonical counts, without a thermodynamic-limit assertion."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229536"), ResolutionKind.Proved)))));

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

    private static Formula BetweenBonds() => Seq(OpenBrace,
        Pair(Num("0"), Num("0")), Comma, Sp, Pair(Num("0"), Num("1")), Comma, Sp,
        Pair(Num("1"), Num("0")), Comma, Sp, Pair(Num("1"), Num("1")), Comma, Sp,
        Pair(Num("1"), Num("2")), Comma, Sp, Pair(Num("2"), Num("1")), Comma, Sp,
        Pair(Num("2"), Num("2")), CloseBrace);

}
