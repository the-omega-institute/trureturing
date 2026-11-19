using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229584StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229584";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("cross-relabel"),DeclarationHandle.Create(Prefix+"cross_relabel"),H("cross_relabel"),
                StatementSource.FromAuthor(Disp(All("e",Call("Equiv.Perm",Call("Fin",Num("3"))),All("p",Call("HardinA229584StripData.Boundary"),All("r",Call("HardinA229584StripData.Row"),Eq(Call("HardinA229584StripData.cross",Call("Function.comp",V("e"),V("p")),Call("Function.comp",V("e"),V("r"))),Call("HardinA229584StripData.cross",V("p"),V("r")))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The boundary transfer preserves this exact equality under the displayed operations."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("horizontal-relabel"),DeclarationHandle.Create(Prefix+"horizontal_relabel"),H("horizontal_relabel"),
                StatementSource.FromAuthor(Disp(All("e",Call("Equiv.Perm",Call("Fin",Num("3"))),All("r",Call("HardinA229584StripData.Row"),Eq(Call("DefectTransfer.bondDefects",Call("HardinA229584StripData.horizontal"),Call("Function.comp",V("e"),V("r")),Call("Function.comp",V("e"),V("r"))),Call("DefectTransfer.bondDefects",Call("HardinA229584StripData.horizontal"),V("r"),V("r"))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The boundary transfer preserves this exact equality under the displayed operations."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("class-relabel"),DeclarationHandle.Create(Prefix+"class_relabel"),H("class_relabel"),
                StatementSource.FromAuthor(Disp(All("e",Call("Equiv.Perm",Call("Fin",Num("3"))),All("p",Call("HardinA229584StripData.Boundary"),All("d",V("Nat"),Eq(Call("HardinA229584StripData.cl",Call("Function.comp",V("e"),V("p")),V("d")),Call("HardinA229584StripData.cl",V("p"),V("d")))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The boundary transfer preserves this exact equality under the displayed operations."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge"),DeclarationHandle.Create(Prefix+"edge"),H("edge"),
                StatementSource.FromAuthor(Disp(All("r",Call("HardinA229584StripData.Row"),All("t",Call("HardinA229584StripData.Row"),Eq(Call("DefectTransfer.bondDefects",Call("HardinA229584StripData.antidiagonal"),V("r"),V("t")),Call("HardinA229584StripData.cross",Call("HardinA229584StripData.boundary",V("r")),V("t"))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The boundary transfer preserves this exact equality under the displayed operations."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal normalized array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229584Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("6"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229584StripData.horizontal"), Call("HardinA229584StripData.antidiagonal"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("6")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("6"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("6"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("6")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("6")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite filter ranges over all arrays. The ordinal i*k+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"),
                DeclarationHandle.Create(Prefix + "finite_certificate"), H("The complete finite transfer certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229584StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229584StripData.terminal"), Call("HardinA229584StripData.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229584StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("r", V("Row"), Imp(Leq(Add(Call("HardinA229584StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229584StripData.Valid", Call("HardinA229584StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229584StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))))))), And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229584StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("s", Call("Fin", Num("32")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Add(Call("HardinA229584StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229584StripData.cl", Call("HardinA229584StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229584StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229584StripData.T"), Call("HardinA229584StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s"))))))), And(All("r", V("Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")), Num("1")), Call("HardinA229584StripData.Valid", Call("HardinA229584StripData.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("32")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")), Num("1")), Eq(Call("HardinA229584StripData.cl", Call("HardinA229584StripData.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229584StripData.initial"), V("s")))), And(And(Eq(App(Call("HardinA229584StripData.W"), Num("0")), Call("HardinA229584StripData.initial")), All("i", Call("Fin", Num("7")), Eq(App(Call("HardinA229584StripData.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229584StripData.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229584StripData.T"))))), Eq(App(Call("HardinA229584StripData.W"), Num("7")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("6561"))), Call("Matrix.vecCons", Num("14580"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("12150"))), Call("Matrix.vecCons", Num("4662"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("805"))), Call("Matrix.vecCons", Num("50"), Call("Matrix.vecEmpty"))))))), V("j")), App(Call("HardinA229584StripData.W"), Call("Fin.mk", Add(Num("1"), Call("Fin.val", V("j")))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 1+j.val and bound 1+j.val < 8."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("powers-table"),
                DeclarationHandle.Create(Prefix + "powers_table"), H("The cached forward prefix"),
                StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("8")),
                    Eq(Forward(Call("Fin.val", V("i"))),
                        Call("HardinA229584StripData.W", V("i")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The eight cached vectors are the exact forward iterates of the one-defect transfer. HardinA229692StripInherited uses this prefix for its leading block."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polynomial-relation"),
                DeclarationHandle.Create(Prefix + "polynomial_relation"), H("The degree-six vector relation"),
                StatementSource.FromAuthor(Disp(Eq(Forward(Add(Num("1"), Num("6"))),
                    SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul",
                        CastInt(App(Coefficients(), V("j"))),
                        Forward(Add(Num("1"), Call("Fin.val", V("j"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The integer coefficient vector is ordered by increasing forward index. HardinA229692StripInherited transports this relation by powers of the same transfer matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The integer recurrence"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("7")))), Sub(Add(Sub(Add(Sub(Mul(Num("50"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("6"))))), Mul(Num("805"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("5")))))), Mul(Num("4662"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("4")))))), Mul(Num("12150"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("3")))))), Mul(Num("14580"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("2")))))), Mul(Num("6561"), CastInt(Call("HardinA229584Strip.a", Add(V("n"), Num("1")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229584"), ResolutionKind.Proved)))));

    private static Formula Forward(Formula n) => Call("DefectTransfer.forward",
        Call("HardinA229584StripData.T"), Call("HardinA229584StripData.initial"), n);
    private static Formula Coefficients() => Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("6561"))),
        Call("Matrix.vecCons", Num("14580"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("12150"))),
        Call("Matrix.vecCons", Num("4662"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("805"))),
        Call("Matrix.vecCons", Num("50"), Call("Matrix.vecEmpty")))))));
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
