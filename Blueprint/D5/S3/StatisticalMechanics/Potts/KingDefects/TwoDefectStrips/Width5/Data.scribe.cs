using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5;
internal sealed class DataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229752");
    private static readonly LibraryNoteRef ZeroBudgetSource = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-five king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(
            Describe.Lean(DescribeId.Create("decidable-valid"),
                DeclarationHandle.Create(Prefix + "instDecidableValid"), H("Decidability of valid residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("d", Call("Nat"), Call("Decidable", Call("Valid", V("p"), V("d"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exported instance supplies decidability to the class certificates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Row"),
                StatementSource.FromAuthor(Disp(Eq(Call("Row"), Arrow(Call("Fin", Num("5")), Call("Fin", Num("4")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 5 -> Fin 4. Rows carry the four labelled colours on five ordered columns."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("horizontal"),
                StatementSource.FromAuthor(Disp(Eq(Call("horizontal"), Call("StripDefects.HardinA229583StripData.horizontal")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 5 x Fin 5). The four ordered bonds join consecutive columns. This horizontal edge set agrees with StripDefects.HardinA229583StripData.horizontal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("between"),
                DeclarationHandle.Create(Prefix + "between"), H("between"),
                StatementSource.FromAuthor(Disp(Eq(Call("between"), SetOf(Pair(Num("0"), Num("0")), Pair(Num("1"), Num("1")), Pair(Num("2"), Num("2")), Pair(Num("3"), Num("3")), Pair(Num("4"), Num("4")), Pair(Num("0"), Num("1")), Pair(Num("1"), Num("2")), Pair(Num("2"), Num("3")), Pair(Num("3"), Num("4")), Pair(Num("1"), Num("0")), Pair(Num("2"), Num("1")), Pair(Num("3"), Num("2")), Pair(Num("4"), Num("3")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 5 x Fin 5). The thirteen ordered bonds comprise five vertical, four diagonal and four antidiagonal bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Valid"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("d", Call("Nat"), Iff(Call("Valid", V("p"), V("d")), And(Leq(V("d"), Num("2")), Leq(Call("DefectTransfer.bondDefects", Call("horizontal"), V("p"), V("p")), Sub(Num("2"), V("d"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("cl"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> Fin 43. The classifier depends only on the row equality pattern and d mod 3, and has 43 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.")))),
            Describe.Lean(DescribeId.Create("proper-successors"),
                DeclarationHandle.Create(Prefix + "properSuccessors"), H("Proper zero-budget successors"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Eq(Call("properSuccessors", V("p")), Call("List.insertionSort", Lam("a", Call("Fin", Num("43")), Lam("b", Call("Fin", Num("43")), Leq(V("a"), V("b")))), Call("List.map", Lam("v", Call("Fin", Num("4")), Call("cl", Lam("j", Call("Fin", Num("5")), Call("Fin.xor", V("v"), App(V("p"), V("j")))), Num("0"))), Call("List.filter", Lam("v", Call("Fin", Num("4")), Member(V("v"), Call("HardinA233166KingStrip.offsetChoices", Word(Num("0"), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), Num("1"))), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), Num("2"))), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), Num("3"))), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), Num("4"))), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), Num("3"))))))), Call("List.finRange", Num("4"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> List (Fin 43). Map the original width-six owner's allowed xor shifts through the existing class map and sort. Width-five rows use the reflected sixth column. Each allowed shift contributes exactly one labelled successor."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Matrix (Fin 43) (Fin 43) Int. This is a 43 by 43 integer matrix. Proper zero-budget rows count properSuccessors at representative rows; all other rows retain their exact defect data. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.")))),
            Describe.Remark(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 43 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.")))),
            Describe.Remark(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 43 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.")))),
            Describe.Remark(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 12 -> Fin 43 -> Int. The table has twelve rows and 43 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).")))),
            Describe.Remark(DescribeId.Create("classlist"),
                DeclarationHandle.Create(Prefix + "classList"), H("classList"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 43 -> List (Fin 43). Certificate.class_counts pins the multiplicity of each class as the corresponding matrix entry. These finite lists describe all successor multiplicities without transcribing the matrix.")))),
            Describe.Lean(DescribeId.Create("successors"),
                DeclarationHandle.Create(Prefix + "successors"), H("successors"),
                StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("d", Call("Nat"), Eq(Call("successors", V("p"), V("d")), Conditional(And(Eq(V("d"), Num("0")), Eq(Call("DefectTransfer.bondDefects", Call("horizontal"), V("p"), V("p")), Num("0"))), Call("properSuccessors", V("p")), Call("List.insertionSort", Lam("a", Call("Fin", Num("43")), Lam("b", Call("Fin", Num("43")), Leq(V("a"), V("b")))), Call("List.filterMap", Lam("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Conditional(Leq(Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r"))), V("d")), Call("some", Call("cl", V("r"), Sub(V("d"), Add(Call("DefectTransfer.bondDefects", Call("between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("horizontal"), V("r"), V("r")))))), Call("none"))), Call("List.ofFn", Lam("i", Call("Fin", Pow(Num("4"), Num("5"))), Call("Equiv.symm", Call("finFunctionFinEquiv"), V("i")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> List (Fin 43). For a horizontally proper source at zero budget use properSuccessors. Otherwise enumerate every labelled next row, retain those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum."))), DescribeRole.Definition),
            ZeroBudgetNode("extend", "The reflected-column extension", "extend",
                "A width-five row is extended by reflecting its penultimate column into the sixth column. The new adjacent square reflects the preceding square, so it adds no new inequality.", DescribeRole.Definition),
            ZeroBudgetNode("raw5", "The width-five zero-defect relation", "raw5",
                "The raw successor relation records zero between-row and horizontal defects for width five.", DescribeRole.Definition),
            ZeroBudgetNode("proper-extend", "Properness is preserved by extension", "proper_extend",
                "The reflected extension has no horizontal defects exactly when the original width-five row has none.", DescribeRole.Theorem),
            ZeroBudgetNode("raw-extend", "Raw successors are preserved by extension", "raw_extend",
                "The width-six owner relation on reflected extensions is equivalent to the width-five raw relation.", DescribeRole.Theorem),
            ZeroBudgetNode("raw-iff-owner", "The restricted owner image", "raw_iff_owner",
                "For every horizontally proper width-five source, every zero-defect successor is the restriction of an owner allowed shift, and every such restriction is a successor. The shift is recovered uniquely as r(0) xor p(0), giving fibre multiplicity one.", DescribeRole.Theorem),
            ZeroBudgetNode("transition-counts", "The zero-temperature transfer row", "transition_counts",
                "For every horizontally proper width-five source and every class column, the zero-budget successor sum equals the width-five transfer row.", DescribeRole.Theorem))));

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
    private static Formula Word(params Formula[] entries) => Seq(Bang, OpenBracket, Seq(entries.SelectMany((a,i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), CloseBracket);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(a), Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula SetOf(params Formula[] entries) => Seq(OpenBrace, Seq(entries.SelectMany((a,i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), CloseBrace);

    private static DocumentBlock ZeroBudgetNode(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(NodeFormula(declaration))), AssessedProvenance.FromRepo(ZeroBudgetSource),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula NodeFormula(string declaration) => declaration switch
    {
        "raw5" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Call("raw5", V("p"), V("r")), Eq(Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))), Num("0"))))),
        "raw_iff_owner" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")), Iff(Call("raw5", V("p"), V("r")), Ex("v", Call("Fin", Num("4")), And(Member(V("v"), Call("HardinA233166KingStrip.offsetChoices", Call("Width6.ZeroTemperature.offsets", Call("extend", V("p"))))), Eq(V("r"), Lam("j", Call("Fin", Num("5")), Call("Fin.xor", V("v"), App(V("p"), V("j"))))))))))),
        "transition_counts" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")), All("s", Call("Fin", Num("43")), Eq(SumOver("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("Width5.Data.cl", V("r"), Sub(Num("0"), Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))))), V("s"))), Typed(Num("1"), Call("Int")), Typed(Num("0"), Call("Int")))), Call("Width5.Data.T", Call("Width5.Data.cl", V("p"), Num("0")), V("s")))))),
        "extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Eq(Call("extend", V("p")), Word(App(V("p"), Num("0")), App(V("p"), Num("1")), App(V("p"), Num("2")), App(V("p"), Num("3")), App(V("p"), Num("4")), App(V("p"), Num("3"))))),
        "proper_extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Eq(Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), Call("extend", V("p")), Call("extend", V("p"))), Num("0")), Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")))),
        "raw_extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Call("Width6.ZeroTemperature.raw", Call("extend", V("p")), Call("extend", V("r"))), Call("raw5", V("p"), V("r"))))),
        _ => throw new System.ArgumentOutOfRangeException(nameof(declaration))
    };

    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x),t)), Sp, Parenthesized(b));

    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists, Sp, Typed(V(x),t), Comma, Sp, Parenthesized(b));
}
