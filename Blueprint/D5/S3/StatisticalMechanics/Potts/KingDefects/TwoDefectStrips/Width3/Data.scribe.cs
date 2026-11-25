using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3;
internal sealed class DataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229750");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-3 king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(
            Describe.Lean(DescribeId.Create("decidable-valid"),
                DeclarationHandle.Create(Prefix + "instDecidableValid"), H("Decidability of valid residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("3")), Call("Fin", Num("4"))), All("d", Call("Nat"), Call("Decidable", Call("Valid", V("p"), V("d"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exported instance supplies decidability to the class certificates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("horizontal"),
                StatementSource.FromAuthor(Disp(Eq(Call("horizontal"), Call("StripDefects.HardinA229581Strip.horizontal")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 3 x Fin 3). The 2 ordered bonds join consecutive columns. This horizontal edge set agrees with StripDefects.HardinA229581Strip.horizontal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("between"),
                DeclarationHandle.Create(Prefix + "between"), H("between"),
                StatementSource.FromAuthor(Disp(Eq(Call("between"), SetOf(Pair(Num("0"), Num("0")), Pair(Num("1"), Num("1")), Pair(Num("2"), Num("2")), Pair(Num("0"), Num("1")), Pair(Num("1"), Num("2")), Pair(Num("1"), Num("0")), Pair(Num("2"), Num("1")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 3 x Fin 3). The 7 ordered bonds comprise 3 vertical, 2 diagonal and 2 antidiagonal bonds. The same seven between-row edges form CrossedStripDefects.HardinA229536Strip.between."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Valid"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("3")), Call("Fin", Num("4"))), All("d", Call("Nat"), Iff(Call("Valid", V("p"), V("d")), And(Leq(V("d"), Num("2")), Leq(Call("DefectTransfer.bondDefects", Call("horizontal"), V("p"), V("p")), Sub(Num("2"), V("d"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233163KingStrip.Boundary -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("cl"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233163KingStrip.Boundary -> Nat -> Fin 9. The classifier depends only on the row equality pattern and d mod 3, and has 9 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.")))),
            Describe.Remark(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Matrix (Fin 9) (Fin 9) Int. This is a 9 by 9 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.")))),
            Describe.Remark(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 9 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.")))),
            Describe.Remark(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 9 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero. This zero-budget indicator is the terminal vector CrossedStripDefects.HardinA229632Strip.terminal.")))),
            Describe.Remark(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 9 -> Fin 9 -> Int. The table has nine rows and 9 columns. Forward.structural_certificate pins W(0), eight forward steps and the six-term relation at W(8).")))),
            Describe.Remark(DescribeId.Create("classlist"),
                DeclarationHandle.Create(Prefix + "classList"), H("classList"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 9 -> List (Fin 9). Certificate.class_counts pins the multiplicity of each remaining class as the corresponding matrix entry. The two productive proper zero-budget classes use empty list placeholders; ZeroTemperature.transition_counts supplies their transfer entries directly from the saturated signed owner. These finite lists describe all successor multiplicities without transcribing the matrix.")))),
            Describe.Lean(DescribeId.Create("successors"),
                DeclarationHandle.Create(Prefix + "successors"), H("successors"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("3")), Call("Fin", Num("4"))), All("d", Call("Nat"), Eq(Call("successors", V("p"), V("d")), Call("List.insertionSort", Lam("a", Call("Fin", Num("9")), Lam("b", Call("Fin", Num("9")), Leq(V("a"), V("b")))), Call("List.filterMap", Lam("r", Arrow(Call("Fin", Num("3")), Call("Fin", Num("4"))), Conditional(Leq(Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r"))), V("d")), Call("some", Call("cl", V("r"), Sub(V("d"), Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r")))))), Call("none"))), Call("List.ofFn", Lam("i", Call("Fin", Pow(Num("4"), Num("3"))), Call("Equiv.symm", Call("finFunctionFinEquiv"), V("i"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233163KingStrip.Boundary -> Nat -> List (Fin 9). Enumerate every labelled next row, retain exactly those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("The zero-budget transfer"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA233163KingStrip.Boundary"), Imp(Call("HardinA233163KingStrip.proper", V("p")), All("s", Call("Fin", Num("9")), Eq(SumOver("r", Call("HardinA233163KingStrip.Boundary"), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("Data.cl", V("r"), Sub(Num("0"), Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))))), V("s"))), Typed(Num("1"), Call("Int")), Typed(Num("0"), Call("Int")))), Call("Data.T", Call("Data.cl", V("p"), Num("0")), V("s")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229750")),
                Blocks(Paragraph(Text("The map beta sends complementary signed colours to the same four-colour label. Every raw boundary has exactly 8 signed preimages, with two independent choices per column. SignedFibres.sum_beta gives the weighted identity with factor 2^3. The signed row predicate is equivalent to zero defects after applying the map. The owner saturated_certificate preserves the productive boundary type and gives the signed rate. Class correspondence transports kind to the two zero-budget classes, so dividing the signed rate by 8 gives the displayed entry. At width 3, the two signed rates are 16 and 8, hence the raw rates are two and one. All sums and matrix entries are integers; the subtraction inside Data.cl is natural subtraction."))), DescribeRole.Theorem),
            Paragraph(Text("The initial and terminal certificates establish the domain interpretation of the table. The Krylov identities normalize the resulting integer entries; the combined certificate retains the domain content.")),
            Describe.Lean(DescribeId.Create("structural-certificate"),
                DeclarationHandle.Create(Prefix + "structural_certificate"), H("Acceptance, initialization and the forward relation"),
                StatementSource.FromAuthor(Disp(And(All("p", Call("HardinA233163KingStrip.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("Data.Valid", V("p"), Call("Fin.val", V("d"))), Eq(Call("Data.terminal", Call("Data.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("s", Call("Fin", Num("9")), Eq(SumOver("r", Call("HardinA233163KingStrip.Boundary"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("Data.cl", V("r"), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), Call("Data.initial", V("s")))), And(And(Eq(Call("Data.W", Num("0")), Call("Data.initial")), All("i", Call("Fin", Num("8")), Eq(Call("Data.W", Call("Fin.succ", V("i"))), Call("Matrix.vecMul", Call("Data.W", Call("Fin.castSucc", V("i"))), Call("Data.T"))))), Eq(Call("Data.W", Num("8")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Neg(Num("8")), Call("Matrix.vecCons", Num("36"), Call("Matrix.vecCons", Neg(Num("66")), Call("Matrix.vecCons", Num("63"), Call("Matrix.vecCons", Neg(Num("33")), Call("Matrix.vecCons", Num("9"), Call("Matrix.vecEmpty"))))))), V("j")), Call("Data.W", Call("Fin.mk", Add(Num("2"), Call("Fin.val", V("j"))))))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every valid row and budget, the terminal entry is the zero-budget indicator. The initial vector counts first rows. W(0)=initial and W(i+1)=W(i)T for i=0,...,7. Finally W(8)=-8W(2)+36W(3)-66W(4)+63W(5)-33W(6)+9W(7). Every identity is kernel checked."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(p.Select(ch => ch >= '0' && ch <= '9'
            ? Num(new string(new[] { ch })) : V(new string(new[] { ch }))).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x),t), Sp, Mapsto, Sp, b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Lam(string x, Formula t, Formula b) => Fn(x, t, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(a), Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula SetOf(params Formula[] entries) => Seq(OpenBrace, Seq(entries.SelectMany((a,i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), CloseBrace);

    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));

    private static Formula Neg(Formula a) => Seq(Minus, a);
}
