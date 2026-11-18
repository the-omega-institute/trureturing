using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4;
internal sealed class DataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229751");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-4 king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(
            Describe.Lean(DescribeId.Create("decidable-valid"),
                DeclarationHandle.Create(Prefix + "instDecidableValid"), H("Decidability of valid residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("4")), Call("Fin", Num("4"))), All("d", Call("Nat"), Call("Decidable", Call("Valid", V("p"), V("d"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exported instance supplies decidability to the class certificates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("horizontal"),
                StatementSource.FromAuthor(Disp(Eq(Call("horizontal"), Call("StripDefects.HardinA229582Strip.horizontal")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 4 x Fin 4). The 3 ordered bonds join consecutive columns. It is defined as StripDefects.HardinA229582Strip.horizontal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("between"),
                DeclarationHandle.Create(Prefix + "between"), H("between"),
                StatementSource.FromAuthor(Disp(Eq(Call("between"), SetOf(Pair(Num("0"), Num("0")), Pair(Num("1"), Num("1")), Pair(Num("2"), Num("2")), Pair(Num("3"), Num("3")), Pair(Num("0"), Num("1")), Pair(Num("1"), Num("2")), Pair(Num("2"), Num("3")), Pair(Num("1"), Num("0")), Pair(Num("2"), Num("1")), Pair(Num("3"), Num("2")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 4 x Fin 4). The 10 ordered bonds comprise 4 vertical, 3 diagonal and 3 antidiagonal bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Valid"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("4")), Call("Fin", Num("4"))), All("d", Call("Nat"), Iff(Call("Valid", V("p"), V("d")), And(Leq(V("d"), Num("2")), Leq(Call("DefectTransfer.bondDefects", Call("horizontal"), V("p"), V("p")), Sub(Num("2"), V("d"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("cl"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Fin 19. The classifier depends only on the row equality pattern and d mod 3, and has 19 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.")))),
            Describe.Remark(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Matrix (Fin 19) (Fin 19) Int. This is a 19 by 19 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.")))),
            Describe.Remark(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 19 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.")))),
            Describe.Remark(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 19 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.")))),
            Describe.Remark(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 12 -> Fin 19 -> Int. The table has twelve rows and 19 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).")))),
            Describe.Remark(DescribeId.Create("classlist"),
                DeclarationHandle.Create(Prefix + "classList"), H("classList"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 19 -> List (Fin 19). Certificate.class_counts pins the multiplicity of each remaining class as the corresponding matrix entry. The two productive proper zero-budget classes use empty list placeholders; ZeroTemperature.transition_counts supplies their transfer entries directly from the saturated signed owner. These finite lists describe all successor multiplicities without transcribing the matrix.")))),
            Describe.Lean(DescribeId.Create("successors"),
                DeclarationHandle.Create(Prefix + "successors"), H("successors"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("4")), Call("Fin", Num("4"))), All("d", Call("Nat"), Eq(Call("successors", V("p"), V("d")), Call("List.insertionSort", Lam("a", Call("Fin", Num("19")), Lam("b", Call("Fin", Num("19")), Leq(V("a"), V("b")))), Call("List.filterMap", Lam("r", Arrow(Call("Fin", Num("4")), Call("Fin", Num("4"))), Conditional(Leq(Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r"))), V("d")), Call("some", Call("cl", V("r"), Sub(V("d"), Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r")))))), Call("none"))), Call("List.ofFn", Lam("i", Call("Fin", Pow(Num("4"), Num("4"))), Call("Equiv.symm", Call("finFunctionFinEquiv"), V("i"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is HardinA233164KingStrip.Boundary -> Nat -> List (Fin 19). Enumerate every labelled next row, retain exactly those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum."))), DescribeRole.Definition))));

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
}
