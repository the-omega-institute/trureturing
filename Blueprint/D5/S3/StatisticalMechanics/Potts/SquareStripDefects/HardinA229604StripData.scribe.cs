using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229604StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229604";
    private const string LeanSource = "../../../../../../D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.lean";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Valid"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Iff(Call("HardinA229604StripData.Valid", V("p"), V("d")), Call("HardinA229635State.Valid", V("p"), V("d"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The horizontal defects of the row and the residual budget sum to at most two, as in HardinA229635State.Valid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidable-valid"), DeclarationHandle.Create(Prefix + "decidableValid"),
                H("Residual state decision"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Eq(Typed(Call("HardinA229604StripData.decidableValid", V("p"), V("d")), Call("Decidable", Call("HardinA229604StripData.Valid", V("p"), V("d")))), Call("inferInstanceAs", Call("Decidable", Leq(Add(Call("HardinA229635State.h", V("p")), V("d")), Num("2"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The right-hand side is inferInstanceAs applied to Decidable of the displayed natural-number inequality."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("cl"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Nat"), Eq(Call("HardinA229604StripData.cl", V("p"), V("d")), Conditional(Lt(Num("0"), V("d")), Call("Fin.castAdd", Num("54"), Call("HardinA229457StripData.cl", V("p"), Sub(V("d"), Num("1")))), Conditional(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p")), Num("1")), Typed(Call("Fin.mk", Add(Call("Fin.val", Call("HardinA229457StripData.cl", V("p"), Num("0"))), Num("32"))), Call("Fin", Num("96"))), Typed(Conditional(Lt(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p"))), Num("95"), App(Parenthesized(Lam("c", Call("Nat"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("31"), Num("51")])), Num("74"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("32"), Num("66")])), Num("75"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("33"), Num("65")])), Num("76"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("34"), Num("52")])), Num("77"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("35"), Num("55")])), Num("78"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("36"), Num("62")])), Num("79"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("37")])), Num("80"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("38"), Num("44")])), Num("81"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("39"), Num("49")])), Num("82"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("40"), Num("68")])), Num("83"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("41"), Num("67")])), Num("84"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("42"), Num("50")])), Num("85"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("43")])), Num("86"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("45"), Num("61")])), Num("87"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("46"), Num("56")])), Num("88"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("47"), Num("57")])), Num("89"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("48"), Num("60")])), Num("90"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("53")])), Num("91"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("54"), Num("64")])), Num("92"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("58"), Num("70")])), Num("93"), Conditional(new Formula.Relation(V("c"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([Num("59"), Num("69")])), Num("94"), Num("95")))))))))))))))))))))))), Call("Fin.val", Call("HardinA229635State.cl", V("p"), Num("2"))))), Call("Fin", Num("96")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Positive residual budgets use the one-defect class after subtracting one. At residual zero with at most one horizontal defect, add 32 to the one-defect class. At residual zero with two horizontal defects, use the index of HardinA229635State.cl p 2. At residual zero with more than two horizontal defects, the classifier returns 95. Natural subtraction truncates at zero. Fin.castAdd preserves the index value in a larger finite type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("T"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229604StripData.T"), Arrow(Call("Fin", Num("96")), Arrow(Call("Fin", Num("96")), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For i, j of type Fin 96, guards and offsets use Fin.val i and Fin.val j. All entries are integers. If both values are below 42, apply HardinA229457StripData.T to the Fin 42 indices formed from Fin.val i and Fin.val j using those bounds. If i is at least 42 and j is below 42, the entry is 0.")),
                    Paragraph(Text("The 32 by 54 crossing table has a 10 by 54 upper block. For i below 10 and j at least 42, use row i and column j − 42 of that block. The bottom 22 rows consist of a 22 by 32 integer block followed by 22 zero columns. For i from 20 through 41 and j from 42 through 73, use row i − 20 and column j − 42 of the 22 by 32 block. For the same source rows and j from 74 through 95, the entry is 0.")),
                    Paragraph(Text("For i from 10 through 19 and j from 42 through 73, apply HardinA229457StripData.T to the Fin 42 indices with values Fin.val i − 10 and Fin.val j − 32. For i and j both from 42 through 73, apply it to the Fin 42 indices with values Fin.val i − 32 and Fin.val j − 32. The branch bounds justify each reconstruction.")),
                    Paragraph(Text("For i at least 74 and j from 42 through 51, the entry is at row i − 74 and column j − 42 of the new 22 by 10 integer table. Every other entry is 0. Among Valid states, indices 74 through 95 represent rows with two horizontal defects. The total classifier also sends a constant row at residual zero to class 95, outside Valid because its horizontal cost is five.")),
                    Paragraph(Text("HardinA229604StripClasses.transition_counts identifies the entries with the successor sums. The literal entries are given by [crossing and lastRows](" + LeanSource + "#L79-L137).")),
                    Paragraph(Text("Finite partition refinement of the 96 states, starting with terminal acceptance and splitting by successor counts into each block, stabilizes at 94 classes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("start-image"), DeclarationHandle.Create(Prefix + "startImage"),
                H("start image"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229604StripData.startImage"), Arrow(Call("Fin", Num("127")), Call("Fin", Num("96")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("In the first 31 crossed states, the image is zero. In the next 96 states, subtract 31 from the index and apply cl to the frozen representative HardinA229635State.rep at that index and its frozen residual budget HardinA229635State.budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("initial"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229604StripData.initial"), Arrow(Call("Fin", Num("96")), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For j of type Fin 96, use Fin.val j in the guards and offsets. If Fin.val j is below 42, apply HardinA229457StripData.initial to the Fin 42 index formed from Fin.val j using that bound.")),
                    Paragraph(Text("For j from 42 through 95, sum HardinA229635Transfer.initial over the crossed states s whose startImage s equals j. The first-row horizontal defects and the remaining budget are the same in both geometries. HardinA229604Strip.finite_certificate identifies the resulting entries with the literal first-row counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("terminal"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229604StripData.terminal"), Arrow(Call("Fin", Num("96")), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Fin.append joins 42 zeros, the coordinates HardinA229457StripData.terminal (Fin.natAdd 10 j) for j of type Fin 32, and 22 ones for classes 74 through 95, which represent rows with two horizontal defects among Valid states. For a Valid state, it accepts exactly residual budget zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("W"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229604StripData.W"), Arrow(Call("Fin", Num("25")), Arrow(Call("Fin", Num("96")), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("For k : Fin 25 and j : Fin 96, use the natural values of the indices in these ranges. For j below 42, W k j equals HardinA229457StripData.W (Fin.castAdd 1 k) j, with j read in Fin 42. The cast embeds k into Fin 26 with the same value.")),
                    Paragraph(Text("For j at least 42 and k = 0, W k j is initial j. For j at least 42 and k at least 1, W k j is at row k − 1 and column j − 42 of the new 24 by 54 integer table.")),
                    Paragraph(Text("HardinA229604StripPowers.steps gives the initial row and the product of each preceding row with T. The 24 by 54 table is the literal tail of the Fin.cons argument to [W](" + LeanSource + "#L168)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("leading-block"), DeclarationHandle.Create(Prefix + "leading_block"),
                H("leading block"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("42")), All("j", Call("Fin", Num("42")), Eq(Call("HardinA229604StripData.T", Call("Fin.castAdd", Num("54"), V("i")), Call("Fin.castAdd", Num("54"), V("j"))), Call("HardinA229457StripData.T", V("i"), V("j"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The displayed embeddings identify this whole matrix block with the original one-defect transfer. Fin.castAdd embeds each index with the same value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("terminal-block"), DeclarationHandle.Create(Prefix + "terminal_block"),
                H("terminal block"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("32")), All("j", Call("Fin", Num("32")), Eq(Call("HardinA229604StripData.T", Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("i"))), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("j")))), Call("HardinA229457StripData.T", Call("Fin.natAdd", Num("10"), V("i")), Call("Fin.natAdd", Num("10"), V("j")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The displayed embeddings identify this whole matrix block with the original one-defect transfer. Fin.castAdd embeds each index with the same value."))), DescribeRole.Theorem))));
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
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Lam(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
}
