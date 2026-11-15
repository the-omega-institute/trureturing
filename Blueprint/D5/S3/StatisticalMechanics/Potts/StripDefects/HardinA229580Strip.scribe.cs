using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229580StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229580Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229580";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("type-row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Rows"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.Row"), Arrow(Call("Fin", Num("2")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row lists its colours in column order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("type-boundary"),
                DeclarationHandle.Create(Prefix + "Boundary"), H("Outgoing boundary"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.Boundary"), Arrow(Call("Fin", Num("1")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The tail of a row meets the following row along antidiagonal bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("Horizontal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.horizontal"), Call("Finset.image", Fn("j", Call("Fin", Num("1")), Pair(Call("Fin.castSucc", V("j")), Call("Fin.succ", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antidiagonal"),
                DeclarationHandle.Create(Prefix + "antidiagonal"), H("Antidiagonal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.antidiagonal"), Call("Finset.image", Fn("j", Call("Fin", Num("1")), Pair(Call("Fin.succ", V("j")), Call("Fin.castSucc", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boundary"),
                DeclarationHandle.Create(Prefix + "boundary"), H("Retaining the outgoing tail"),
                StatementSource.FromAuthor(Disp(All("r", V("Row"), Eq(Call("HardinA229580Strip.boundary", V("r")), Call("Fin.tail", V("r")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Column zero does not meet the next row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cross"),
                DeclarationHandle.Create(Prefix + "cross"), H("Defects between rows"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("r", V("Row"), Eq(Call("HardinA229580Strip.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.antidiagonal"), Call("Fin.cons", Num("0"), V("p")), V("r"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inserted zero is outside every antidiagonal bond."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Admissible residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Iff(Call("HardinA229580Strip.Valid", V("p"), V("d")), And(Leq(V("d"), Num("1")), Leq(Call("Finset.card", Call("Finset.filter", Fn("j", Call("Fin", Num("0")), Eq(App(V("p"), Call("Fin.castSucc", V("j"))), App(V("p"), Call("Fin.succ", V("j"))))), Call("Finset.univ"))), Sub(Num("1"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Colour permutation classes"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Eq(Call("HardinA229580Strip.cl", V("p"), V("d")), Conditional(Eq(V("d"), Num("1")), Num("0"), Num("1"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Only equality relations between boundary colours affect continuation counts. The classes also record the remaining defect budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Class transfer matrix"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.T"), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("4"), Call("Matrix.vecCons", Num("4"), Call("Matrix.vecEmpty"))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("4"), Call("Matrix.vecEmpty"))), Call("Matrix.vecEmpty")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("Initial labelled row counts"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.initial"), Call("Matrix.vecCons", Num("6"), Call("Matrix.vecCons", Num("3"), Call("Matrix.vecEmpty")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Terminal acceptance weights"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.terminal"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("1"), Call("Matrix.vecEmpty")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("Forward transfer table"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229580Strip.W"), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("6"), Call("Matrix.vecCons", Num("3"), Call("Matrix.vecEmpty"))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("36"), Call("Matrix.vecEmpty"))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("96"), Call("Matrix.vecCons", Num("240"), Call("Matrix.vecEmpty"))), Call("Matrix.vecEmpty"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal normalized array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229580Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("2"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229580Strip.horizontal"), Call("HardinA229580Strip.antidiagonal"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("2")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("2"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("2"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("2")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("2")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite filter ranges over all arrays. The ordinal i*k+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"),
                DeclarationHandle.Create(Prefix + "finite_certificate"), H("The complete finite transfer certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229580Strip.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229580Strip.terminal"), Call("HardinA229580Strip.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229580Strip.Valid", V("p"), Call("Fin.val", V("d"))), All("r", V("Row"), Imp(Leq(Add(Call("HardinA229580Strip.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229580Strip.Valid", Call("HardinA229580Strip.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229580Strip.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r")))))))))), And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229580Strip.Valid", V("p"), Call("Fin.val", V("d"))), All("s", Call("Fin", Num("2")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Add(Call("HardinA229580Strip.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229580Strip.cl", Call("HardinA229580Strip.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229580Strip.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229580Strip.T"), Call("HardinA229580Strip.cl", V("p"), Call("Fin.val", V("d"))), V("s"))))))), And(All("r", V("Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r")), Num("1")), Call("HardinA229580Strip.Valid", Call("HardinA229580Strip.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("2")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r")), Num("1")), Eq(Call("HardinA229580Strip.cl", Call("HardinA229580Strip.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229580Strip.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229580Strip.initial"), V("s")))), And(And(Eq(App(Call("HardinA229580Strip.W"), Num("0")), Call("HardinA229580Strip.initial")), All("i", Call("Fin", Num("2")), Eq(App(Call("HardinA229580Strip.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229580Strip.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229580Strip.T"))))), Eq(App(Call("HardinA229580Strip.W"), Num("2")), SumOver("j", Call("Fin", Num("2")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("16"))), Call("Matrix.vecCons", Num("8"), Call("Matrix.vecEmpty"))), V("j")), App(Call("HardinA229580Strip.W"), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("j")))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 0+j and bound 0+j < 3."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The integer recurrence"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229580Strip.a", Add(V("n"), Num("4")))), Sub(Mul(Num("8"), CastInt(Call("HardinA229580Strip.a", Add(V("n"), Num("3"))))), Mul(Num("16"), CastInt(Call("HardinA229580Strip.a", Add(V("n"), Num("2")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229580"), ResolutionKind.Proved)))));

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
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}
