using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693;

internal sealed class HardinA229693StripTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.";
    private const string Note = "D5/L/SpinModels/hardin2013a229693";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect strip transfer.", H("Exact two-defect strip transfer"),
        Blocks(
            Describe.Lean(DescribeId.Create("exhausted-class"),
                DeclarationHandle.Create(Prefix + "exhaustedClass"), H("Classes at budget zero"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.exhaustedClass"), Arrow(Call("HardinA229585StripData.Boundary"), Call("Fin", Num("96")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("If Valid(p,1) holds, let i be the value of the A229585 class of p at budget zero. The return value is i minus 16 in Fin 96 when i is at least 16, and zero otherwise. If Valid(p,1) fails, use the A229635 first-occurrence equality-pattern index. Its first 40 entries are the lexicographically ordered canonical six-cell boundaries with exactly two adjacent equalities. Return 56 plus the residue of that index modulo 40. A pattern absent from the 40 entries in this branch has more than two adjacent equalities. Its equality mask is absent from the 96 A229635 representatives, whose lookup returns 96 before reduction modulo 96. The resulting index is zero, so the exhausted class is 56."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Class of a boundary and budget"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), Eq(Call("HardinA229693StripTransfer.cl", V("p"), V("d")), Conditional(Eq(V("d"), Num("0")), Call("Fin.natAdd", Num("72"), Call("HardinA229693StripTransfer.exhaustedClass", V("p"))), Call("Fin.castAdd", Num("96"), Call("HardinA229585StripData.cl", V("p"), Sub(V("d"), Num("1")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A positive budget d uses the A229585 boundary class at budget d minus one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exit-read"),
                DeclarationHandle.Create(Prefix + "exitRead"), H("Column indices of the exhausted block"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.exitRead"), Arrow(Call("Fin", Num("96")), Call("Fin", Num("108")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This 96-entry map selects the leading column at indices below 72 and one of 36 stored profiles at indices from 72 through 107. The transition multiplicity formula pins the selected profile to its exhausted destination class."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Transfer matrix"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.T"), Call("Matrix", Call("Fin", Num("168")), Call("Fin", Num("168")), V("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading block is the A229585 transfer matrix. The lower left block is zero. The right blocks count rows that spend exactly the remaining budget. The 16 upper-right rows selected by zeroBudgetClass use the exhausted columns of the corresponding A229585 row followed by 40 zeros. In the other upper-right rows, 24 columns use entries of the leading block and the others use 36 multiplicity profiles. Within the lower right block, the original exhausted sources use the exhausted rows and columns of A229585, extended by zero columns. The transition counts formula gives the entries at each admissible source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("First-row weights"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.initial"), Arrow(Call("Fin", Num("168")), V("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first 72 entries are the A229585 initial weights. The remaining entries count labelled rows with exactly two horizontal defects, grouped by exhausted boundary class. The strip counting formula uses this vector on the left."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Acceptance weights"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229693StripTransfer.terminal"), Call("Fin.append", TypeOf(Num("0"), Arrow(Call("Fin", Num("72")), V("Int"))), TypeOf(Num("1"), Arrow(Call("Fin", Num("96")), V("Int"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A completed strip is accepted when its remaining budget is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("Multiplicity of a successor class"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), All("s", Call("Fin", Num("168")), Imp(Or(Call("HardinA229635State.Valid", V("p"), V("d")),
                    Or(And(Eq(V("d"), Num("0")), Lt(Call("Fin.val", V("s")), Num("72"))),
                        And(Eq(V("d"), Num("1")), Lt(Call("Fin.val", V("s")), Num("16"))))), Eq(SumOver("r", Call("HardinA229585StripData.Row"), Conditional(And(Leq(Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), V("d")), Eq(Call("HardinA229693StripTransfer.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(V("d"), Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))))), V("s"))), CastInt(Num("1")), CastInt(Num("0")))), App(Call("HardinA229693StripTransfer.T"), Call("HardinA229693StripTransfer.cl", V("p"), V("d")), V("s"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each admissible next row contributes one to the multiplicity of its class after spending its horizontal and antidiagonal defects.")),
                    Paragraph(Text("At budget zero, both entries vanish below destination 72 for every boundary. At budget one, both entries vanish below destination 16 because the old zero-budget block has no transitions to those destinations. A constant boundary supplies an example of an inadmissible budget in each case."))), DescribeRole.Theorem),
            Node("matchCost", "Cost of a colour match",
                Arrow(Call("Option", Fin3), Arrow(Fin3, V("Nat"))),
                "An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour.", DescribeRole.Definition),
            Node("completionCost", "Cost of a completion",
                All("k", V("Nat"), Arrow(Boundary, Arrow(Call("Option", Fin3), Arrow(Row, V("Nat"))))),
                "Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours.", DescribeRole.Definition),
            Node("completionRows", "Pruned completion list",
                All("k", V("Nat"), Arrow(Boundary, Arrow(Call("Option", Fin3), Arrow(V("Nat"), Call("List", Row))))),
                "Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget.", DescribeRole.Definition),
            Node("completionRows_count", "Multiplicity of qualifying rows",
                All("k", V("Nat"), All("p", Boundary, All("b", Call("Option", Fin3),
                    All("d", V("Nat"), All("f", Arrow(Row, V("Bool")),
                        Eq(Call("List.countP", V("f"), Call("completionRows", V("p"), V("b"), V("d"))),
                            Seq(Sum, Underscore, Grp(V("r"), Colon, Sp, Row), Sp, Parenthesized(Seq(
                                V("if"), Sp, Parenthesized(Eq(Call("completionCost", V("p"), V("b"), V("r")), V("d"))),
                                Sp, Land, Sp, Parenthesized(Eq(Call("f", V("r")), V("true"))),
                                Sp, V("then"), Sp, D(1), Sp, V("else"), Sp, D(0)))))))))),
                "The sum counts each qualifying row once.", DescribeRole.Theorem),
            Node("completionCodes", "Pruned list in base three",
                Arrow(Call("List", Call("Option", Fin3)), Arrow(Call("Option", Fin3), Arrow(V("Nat"), Call("List", V("Nat"))))),
                "Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with x plus three times c.", DescribeRole.Definition),
            Node("rowCode_cons", "Code of a row with a new head",
                All("k", V("Nat"), All("x", Fin3, All("r", Arrow(Call("Fin", V("k")), Fin3),
                    Eq(Code(Call("Fin.cons", V("x"), V("r"))), Add(Call("Fin.val", V("x")), new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, Code(V("r")))))))),
                "The leading cell is the least significant digit of the code.", DescribeRole.Theorem),
            Node("completionCodes_eq", "Agreement of the two lists",
                All("k", V("Nat"), All("p", Boundary, All("b", Call("Option", Fin3), All("d", V("Nat"),
                    Eq(Call("completionCodes", Call("List.ofFn", V("p")), V("b"), V("d")),
                        Call("List.map", Seq(LambdaLower, Sp, V("r"), Sp, Mapsto, Sp, Code(V("r"))),
                            Call("completionRows", V("p"), V("b"), V("d")))))))),
                "The numeric enumerator returns the codes of the pruned completion list in the same order.", DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula TypeOf(Formula a, Formula b) => Seq(a, Sp, Colon, Sp, b);
    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(declaration.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(role == DescribeRole.Definition ? Seq(V(declaration), Colon, Sp, formula) : formula)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text(prose))), role);

    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Boundary => Arrow(Call("Fin", V("k")), Call("Option", Fin3));
    private static Formula Row => Arrow(Call("Fin", Add(V("k"), D(1))), Fin3);
    private static Formula Code(Formula row) => Call("Fin.val", Call("finFunctionFinEquiv", row));
}
