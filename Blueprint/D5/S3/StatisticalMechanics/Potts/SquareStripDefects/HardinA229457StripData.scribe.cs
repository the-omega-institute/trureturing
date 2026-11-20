using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229457StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229457";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Valid"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Iff(Call("HardinA229457StripData.Valid", V("p"), V("d")), Call("HardinA229532StripData.Valid", V("p"), V("d"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The imported predicate requires d ≤ 1 and bondDefects horizontal p p ≤ 1 - d, where natural subtraction truncates at zero. The residual budget is bounded by one and the current row can use only its complementary part."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidable-valid"), DeclarationHandle.Create(Prefix + "decidableValid"),
                H("Residual state decision"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Eq(Typed(Call("HardinA229457StripData.decidableValid", V("p"), V("d")), Call("Decidable", Call("HardinA229457StripData.Valid", V("p"), V("d")))), Call("inferInstanceAs", Call("Decidable", Call("HardinA229532StripData.Valid", V("p"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The right-hand side is inferInstanceAs applied to Decidable of HardinA229532StripData.Valid p d. The imported predicate supplies its existing decision instance."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("cl"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Eq(Call("HardinA229457StripData.cl", V("p"), V("d")), Typed(Conditional(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p")), Num("0")), Conditional(Lt(Num("0"), V("d")), Call("Fin.castAdd", Num("32"), Call("ProperTransfer.cl", V("p"))), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("10"), Call("ProperTransfer.cl", V("p"))))), App(Parenthesized(Lam("c", Call("Nat"), Conditional(Eq(Call("HardinA229532StripData.cl", V("p"), V("d")), Num("26")), Num("20"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("1093"), Num("19520")])), Num("21"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("8533"), Num("19482")])), Num("22"), Conditional(Eq(Call("HardinA229532StripData.cl", V("p"), V("d")), Num("29")), Num("23"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("2185"), Num("16772")])), Num("24"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("8329"), Num("16770")])), Num("25"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("1297"), Num("16472")])), Num("26"), Conditional(Eq(Call("HardinA229532StripData.cl", V("p"), V("d")), Num("25")), Num("27"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("10902")])), Num("28"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("646"), Num("10880")])), Num("29"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("10774")])), Num("30"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("774"), Num("10760")])), Num("31"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("6354"), Num("9396")])), Num("32"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("4290"), Num("9376")])), Num("33"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("6162"), Num("8244")])), Num("34"), Conditional(Eq(Call("HardinA229532StripData.cl", V("p"), V("d")), Num("22")), Num("35"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("1188"), Num("6336")])), Num("36"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("2340"), Num("6156")])), Num("37"), Conditional(Eq(Call("HardinA229532StripData.cl", V("p"), V("d")), Num("21")), Num("38"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("1200"), Num("4304")])), Num("39"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("776")])), Num("40"), Num("41")))))))))))))))))))))))), Call("HardinA229532StripData.equalityPatternCode", V("p")))), Call("Fin", Num("42")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The five tests for output classes 20, 23, 27, 35 and 38 call HardinA229532StripData.cl p d with target indices 26, 29, 25, 22 and 21 respectively. The other tests use the equality-pattern code from HardinA229532StripData, with a bit for each column pair in lexicographic order. Reflection pairs are retained separately whenever the later budget extension distinguishes them. Fin.castAdd preserves an index value in a larger finite type; Fin.natAdd adds its leading natural offset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("T"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229457StripData.T"), Arrow(Call("Fin", Num("42")), Arrow(Call("Fin", Num("42")), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For i, j : Fin 42, write i and j for their natural values in the index ranges below. All matrix entries are integers. The indices 0 through 9 and 10 through 19 are the proper-row classes with positive and zero residual budget, respectively. Indices 20 through 41 are the rows with one horizontal defect.")),
                    Paragraph(Text("If i and j are both below 10, the entry is ProperTransfer.T i j. If i is below 10 and j is at least 10, the entry is at row i and column j − 10 of the new 10 by 32 crossing table.")),
                    Paragraph(Text("If i and j are both in 10 through 19, the entry is ProperTransfer.T (i − 10) (j − 10). If i is at least 20 and j is in 10 through 19, the entry is at row i − 20 and column j − 10 of the new 22 by 10 table for rows with one horizontal defect. Every other entry is 0.")),
                    Paragraph(Text("HardinA229457StripClasses.transition_counts pins the entries of the two new integer tables to the successor sums."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("initial"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229457StripData.initial"), Arrow(Call("Fin", Num("42")), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For j : Fin 42, the following cases use the natural value of j. For j below 10, let d(j) = HardinA233127SquareStrip.distribution 0 (j + 1) and d₀ = HardinA233127SquareStrip.distribution 0 0. At j = 0 the entry is (6 · d(j) + 3 · d₀) / 8. At j in 1 through 9 it is 6 · d(j) / 8. Both divisions are in Int. The entries at j in 10 through 19 are 0.")),
                    Paragraph(Text("In the final block, the entries at j = 20, 23, 27, 35 and 38 are the entries of HardinA229532StripData.initial at 26, 29, 25, 22 and 21, respectively. The remaining entries are 6 at j = 28, 30, 40 and 41, and 12 at every other index in 20 through 41.")),
                    Paragraph(Text("HardinA229457Strip.finite_certificate identifies each entry with its literal first-row count."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("terminal"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229457StripData.terminal"), Matrix(new Formula[][] { new Formula[] { Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1") } })))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This one by 42 row vector accepts precisely residual budget zero. Fin.append joins ten zeros, the ten proper-coordinate entries of HardinA233127SquareStrip.w 0, and 22 ones for the rows with a horizontal defect."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("W"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229457StripData.W"), Arrow(Call("Fin", Num("26")), Arrow(Call("Fin", Num("42")), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For k : Fin 26 and j : Fin 42, use their natural values in the index arithmetic. For j below 10, W k j equals initial j times HardinA233127SquareStrip.w k (j + 1), divided in Int by 64 raised to k. This block inherits the scanner vectors with the first-row multiplicity and scale shown here.")),
                    Paragraph(Text("For j at least 10 and k = 0, W k j is initial j. For j at least 10 and k at least 1, W k j is at row k − 1 and column j − 10 of the new 25 by 32 integer table.")),
                    Paragraph(Text("HardinA229457StripPowers.steps pins the new rows by giving the initial row and the product of each preceding row with T."))), DescribeRole.Definition))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
    private static Formula Matrix(params Formula[][] a) => Seq(new Formula[] { Begin, Grp(F.Id("pmatrix")) }.Concat(a.SelectMany((row,i) => (i == 0 ? Array.Empty<Formula>() : new Formula[] {RowBreak}).Concat(row.SelectMany((x,j) => j==0 ? new[] {x} : new[] {Amp,x})))).Concat(new Formula[] {End, Grp(F.Id("pmatrix"))}).ToArray());
    private static Formula Lam(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
}
