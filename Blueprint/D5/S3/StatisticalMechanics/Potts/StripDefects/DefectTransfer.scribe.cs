using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class DefectTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.";
    private const string Note = "D5/L/SpinModels/hardin2013a229580";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Rows have q colours and k columns. H and V are arbitrary finite sets of in-row and between-row bonds. Exact defect counts, arbitrary residual targets and boundary quotients are handled uniformly. No geometric adjacency or colour count is fixed.")),
            Describe.Lean(DescribeId.Create("type-row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Finite colour rows"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), Eq(Call("DefectTransfer.Row", V("q"), V("k")), Arrow(Call("Fin", V("k")), Call("Fin", V("q")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Both the colour count and the row width are arbitrary natural numbers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bonddefects"),
                DeclarationHandle.Create(Prefix + "bondDefects"), H("Counting monochromatic bonds"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("E", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("r", Call("DefectTransfer.Row", V("q"), V("k")), All("t", Call("DefectTransfer.Row", V("q"), V("k")), Eq(Call("DefectTransfer.bondDefects", V("E"), V("r"), V("t")), Call("Finset.card", Call("Finset.filter", Fn("z", Product(Call("Fin", V("k")), Call("Fin", V("k"))), Eq(App(V("r"), Call("Prod.fst", V("z"))), App(V("t"), Call("Prod.snd", V("z"))))), V("E"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A bond is specified by its ordered pair of column indices. Equality contributes one defect."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("taildefects"),
                DeclarationHandle.Create(Prefix + "tailDefects"), H("Defects after an outgoing row"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("r", Call("DefectTransfer.Row", V("q"), V("k")), And(Eq(Call("DefectTransfer.tailDefects", V("H"), V("V"), V("r"), Call("List.nil")), Num("0")), All("t", Call("DefectTransfer.Row", V("q"), V("k")), All("rs", Call("List", Call("DefectTransfer.Row", V("q"), V("k"))), Eq(Call("DefectTransfer.tailDefects", V("H"), V("V"), V("r"), Call("List.cons", V("t"), V("rs"))), Add(Add(Call("DefectTransfer.bondDefects", V("V"), V("r"), V("t")), Call("DefectTransfer.bondDefects", V("H"), V("t"), V("t"))), Call("DefectTransfer.tailDefects", V("H"), V("V"), V("t"), V("rs")))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each new row contributes its in-row bonds and the bonds from the preceding row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("defects"),
                DeclarationHandle.Create(Prefix + "defects"), H("Total defects in a word of rows"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), And(Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.nil")), Num("0")), All("r", Call("DefectTransfer.Row", V("q"), V("k")), All("rs", Call("List", Call("DefectTransfer.Row", V("q"), V("k"))), Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.cons", V("r"), V("rs"))), Add(Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")), Call("DefectTransfer.tailDefects", V("H"), V("V"), V("r"), V("rs"))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The empty strip has zero defects. The first row contributes only in-row bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literalcount"),
                DeclarationHandle.Create(Prefix + "literalCount"), H("The literal labelled count"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("D", V("Nat"), All("n", V("Nat"), Eq(Call("DefectTransfer.literalCount", V("H"), V("V"), V("D"), V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", V("k"))), Call("Fin", V("q"))), Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", V("k")), App(V("A"), Pair(V("i"), V("j"))))))), V("D"))), Call("Finset.univ")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite filter enumerates all arrays on the product of the row and column index sets. The defect target D is unrestricted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relabel-defects"),
                DeclarationHandle.Create(Prefix + "relabel_defects"), H("Invariance under colour permutations"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("e", Call("Equiv.Perm", Call("Fin", V("q"))), All("rs", Call("List", Call("DefectTransfer.Row", V("q"), V("k"))), Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.map", Fn("r", Call("DefectTransfer.Row", V("q"), V("k")), Call("Function.comp", V("e"), V("r"))), V("rs"))), Call("DefectTransfer.defects", V("H"), V("V"), V("rs"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A permutation preserves equality at the two endpoints of every bond."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("constant-defects"),
                DeclarationHandle.Create(Prefix + "constant_defects"), H("The defect count of a constant strip"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("c", Call("Fin", V("q")), All("n", V("Nat"), Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.replicate", Add(V("n"), Num("1")), Call("Function.const", Call("Fin", V("k")), V("c")))), Add(Call("Finset.card", V("H")), Mul(V("n"), Add(Call("Finset.card", V("V")), Call("Finset.card", V("H")))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every bond is monochromatic in a constant strip. There are n+1 in-row copies and n between-row copies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continuation"),
                DeclarationHandle.Create(Prefix + "continuation"), H("Exact residual-budget continuations"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("B", V("Type"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("P", Arrow(Call("DefectTransfer.Row", V("q"), V("k")), V("B")), All("C", Arrow(V("B"), Arrow(Call("DefectTransfer.Row", V("q"), V("k")), V("Nat"))), All("p", V("B"), All("d", V("Nat"), And(Eq(Call("DefectTransfer.continuation", V("H"), V("P"), V("C"), Num("0"), V("p"), V("d")), Conditional(Eq(V("d"), Num("0")), Num("1"), Num("0"))), All("n", V("Nat"), Eq(Call("DefectTransfer.continuation", V("H"), V("P"), V("C"), Add(V("n"), Num("1")), V("p"), V("d")), SumOver("r", Call("DefectTransfer.Row", V("q"), V("k")), Conditional(Leq(Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r"))), V("d")), Call("DefectTransfer.continuation", V("H"), V("P"), V("C"), V("n"), App(V("P"), V("r")), Sub(V("d"), Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r"))))), Num("0")))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("P retains a boundary; C counts between-row defects from that boundary. A row exceeding the residual budget contributes zero. Natural subtraction is used only under this budget test."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lumped-count"),
                DeclarationHandle.Create(Prefix + "lumped_count"), H("Finite quotients preserve the literal count"),
                StatementSource.FromAuthor(Disp(All("q", V("Nat"), All("k", V("Nat"), All("B", V("Type"), All("H", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), All("P", Arrow(Call("DefectTransfer.Row", V("q"), V("k")), V("B")), All("C", Arrow(V("B"), Arrow(Call("DefectTransfer.Row", V("q"), V("k")), V("Nat"))), All("V", Call("Finset", Product(Call("Fin", V("k")), Call("Fin", V("k")))), AllInst("S", V("Type"), All("Valid", Arrow(V("B"), Arrow(V("Nat"), V("Prop"))), All("cl", Arrow(V("B"), Arrow(V("Nat"), V("S"))), All("T", Call("Matrix", V("S"), V("S"), V("Int")), All("v", Arrow(V("S"), V("Int")), All("e", Arrow(V("S"), V("Int")), All("D", V("Nat"), Imp(And(All("r", Call("DefectTransfer.Row", V("q"), V("k")), All("t", Call("DefectTransfer.Row", V("q"), V("k")), Eq(Call("DefectTransfer.bondDefects", V("V"), V("r"), V("t")), App(V("C"), App(V("P"), V("r")), V("t"))))), And(All("p", V("B"), All("d", V("Nat"), Imp(App(V("Valid"), V("p"), V("d")), Eq(App(V("e"), App(V("cl"), V("p"), V("d"))), Conditional(Eq(V("d"), Num("0")), Num("1"), Num("0")))))), And(All("p", V("B"), All("d", V("Nat"), Imp(App(V("Valid"), V("p"), V("d")), All("r", Call("DefectTransfer.Row", V("q"), V("k")), Imp(Leq(Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r"))), V("d")), App(V("Valid"), App(V("P"), V("r")), Sub(V("d"), Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")))))))))), And(All("p", V("B"), All("d", V("Nat"), Imp(App(V("Valid"), V("p"), V("d")), All("s", V("S"), Eq(SumOver("r", Call("DefectTransfer.Row", V("q"), V("k")), Conditional(And(Leq(Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r"))), V("d")), Eq(App(V("cl"), App(V("P"), V("r")), Sub(V("d"), Add(App(V("C"), V("p"), V("r")), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(V("T"), App(V("cl"), V("p"), V("d")), V("s"))))))), And(All("r", Call("DefectTransfer.Row", V("q"), V("k")), Imp(Leq(Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")), V("D")), App(V("Valid"), App(V("P"), V("r")), Sub(V("D"), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")))))), All("s", V("S"), Eq(SumOver("r", Call("DefectTransfer.Row", V("q"), V("k")), Conditional(And(Leq(Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")), V("D")), Eq(App(V("cl"), App(V("P"), V("r")), Sub(V("D"), Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(V("v"), V("s"))))))))), All("n", V("Nat"), Eq(CastInt(Call("DefectTransfer.literalCount", V("H"), V("V"), V("D"), Add(V("n"), Num("1")))), Call("dotProduct", V("v"), Call("Matrix.mulVec", Pow(V("T"), V("n")), V("e")))))))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("S is any finite type with its finite and equality instances. The premises state boundary factorization, terminal acceptance, budget preservation, every transition-class count, initial admissibility and every initial-class count. Decomposing arrays into a first row and successive continuations proves the equality, with the natural count cast to an integer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forward"),
                DeclarationHandle.Create(Prefix + "forward"), H("Forward row weights"),
                StatementSource.FromAuthor(Disp(AllInst("S", V("Type"), All("T", Call("Matrix", V("S"), V("S"), V("Int")), All("v", Arrow(V("S"), V("Int")), And(Eq(Call("DefectTransfer.forward", V("T"), V("v"), Num("0")), V("v")), All("n", V("Nat"), Eq(Call("DefectTransfer.forward", V("T"), V("v"), Add(V("n"), Num("1"))), Call("Matrix.vecMul", Call("DefectTransfer.forward", V("T"), V("v"), V("n")), V("T")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("S is finite. Each step multiplies a row of weights by T."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("forward-eq"),
                DeclarationHandle.Create(Prefix + "forward_eq"), H("Forward weights are matrix powers"),
                StatementSource.FromAuthor(Disp(AllInst("S", V("Type"), All("T", Call("Matrix", V("S"), V("S"), V("Int")), All("v", Arrow(V("S"), V("Int")), All("n", V("Nat"), Eq(Call("DefectTransfer.forward", V("T"), V("v"), V("n")), Call("Matrix.vecMul", V("v"), Pow(V("T"), V("n")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("S is finite. Associativity identifies recursive forward weights with the corresponding matrix power."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forward-shift"),
                DeclarationHandle.Create(Prefix + "forward_shift"), H("Propagating an initial polynomial relation"),
                StatementSource.FromAuthor(Disp(AllInst("S", V("Type"), All("T", Call("Matrix", V("S"), V("S"), V("Int")), All("v", Arrow(V("S"), V("Int")), All("e", Arrow(V("S"), V("Int")), All("d", V("Nat"), All("b", V("Nat"), All("c", Arrow(Call("Fin", V("d")), V("Int")), Imp(Eq(Call("DefectTransfer.forward", V("T"), V("v"), Add(V("b"), V("d"))), SumOver("j", Call("Fin", V("d")), Call("HSMul.hSMul", App(V("c"), V("j")), Call("DefectTransfer.forward", V("T"), V("v"), Add(V("b"), Call("Fin.val", V("j"))))))), All("n", V("Nat"), Eq(Call("dotProduct", V("v"), Call("Matrix.mulVec", Pow(V("T"), Add(Add(V("n"), V("b")), V("d"))), V("e"))), SumOver("j", Call("Fin", V("d")), Mul(App(V("c"), V("j")), Call("dotProduct", V("v"), Call("Matrix.mulVec", Pow(V("T"), Add(Add(V("n"), V("b")), Call("Fin.val", V("j")))), V("e"))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("S is finite. Multiplying the initial vector relation by any further power of T preserves it, and taking its dot product with any terminal vector gives the shifted scalar relation."))), DescribeRole.Theorem))));

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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula AllInst(string n, Formula t, Formula b) => All(n, t,
        Seq(OpenBracket, Call("Fintype", V(n)), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", V(n)), CloseBracket, Comma, Sp, Parenthesized(b)));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}
