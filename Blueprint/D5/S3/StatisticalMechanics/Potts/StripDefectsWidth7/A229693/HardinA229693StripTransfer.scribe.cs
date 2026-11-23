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
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Admissible residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), Iff(Call("HardinA229693StripTransfer.Valid", V("p"), V("d")), And(Leq(V("d"), Num("2")), Leq(Call("Finset.card", Call("Finset.filter", Fn("j", Call("Fin", Num("5")), Eq(App(V("p"), Call("Fin.castSucc", V("j"))), App(V("p"), Call("Fin.succ", V("j"))))), Call("Finset.univ"))), Sub(Num("2"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The number of adjacent equalities in the six-cell boundary is at most the number of defects already used."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exhausted-class"),
                DeclarationHandle.Create(Prefix + "exhaustedClass"), H("Classes at budget zero"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.exhaustedClass"), Arrow(Call("HardinA229585StripData.Boundary"), Call("Fin", Num("96")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first 56 classes are the exhausted classes of A229585 in their original order. The next 40 classes use the equality patterns of boundaries with two adjacent equalities. Each pattern code lists colours in order of first occurrence and interprets them as base-three digits, starting with the least significant digit. Nat.mod selects the residue of the index in the pattern list modulo 40. The transition counts formula gives the outgoing multiplicities of each admissible boundary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Class of a boundary and budget"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), Eq(Call("HardinA229693StripTransfer.cl", V("p"), V("d")), Conditional(Eq(V("d"), Num("0")), Call("Fin.natAdd", Num("72"), Call("HardinA229693StripTransfer.exhaustedClass", V("p"))), Call("Fin.castAdd", Num("96"), Call("HardinA229585StripData.cl", V("p"), Sub(V("d"), Num("1")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A positive budget d uses the A229585 boundary class at budget d minus one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Transfer matrix"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.T"), Call("Matrix", Call("Fin", Num("168")), Call("Fin", Num("168")), V("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading block is the A229585 transfer matrix. The lower left block is zero. The right blocks count rows that spend exactly the remaining budget. In the upper right block, 24 columns take their multiplicities from columns of the leading block. The remaining columns use 36 distinct multiplicity profiles. Within the lower right block, the original exhausted sources use the exhausted rows and columns of A229585, extended by zero columns. The transition counts formula gives the entries at each admissible source."))), DescribeRole.Definition),
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
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), Imp(Call("HardinA229693StripTransfer.Valid", V("p"), V("d")), All("s", Call("Fin", Num("168")), Eq(SumOver("r", Call("HardinA229585StripData.Row"), Conditional(And(Leq(Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), V("d")), Eq(Call("HardinA229693StripTransfer.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(V("d"), Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))))), V("s"))), CastInt(Num("1")), CastInt(Num("0")))), App(Call("HardinA229693StripTransfer.T"), Call("HardinA229693StripTransfer.cl", V("p"), V("d")), V("s"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each admissible next row contributes one to the multiplicity of its class after spending its horizontal and antidiagonal defects.")),
                    Paragraph(Text("Both bounds in the admissibility condition matter. With budget zero and a constant zero boundary, the two rows alternating colours one and two both contribute to class 85, whose matrix entry is one. With budget three and boundary (0, 1, 0, 1, 0, 1), the row (0, 2, 1, 2, 1, 2, 1) contributes to class zero, whose matrix entry is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-transfer"),
                DeclarationHandle.Create(Prefix + "count_transfer"), H("The labelled strip count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("DefectTransfer.literalCount", Parenthesized(Seq(V("q"), Sp, Colon, F.Eq, Sp, Num("3"))), Call("HardinA229585StripData.horizontal"), Call("HardinA229585StripData.antidiagonal"), Num("2"), Add(V("n"), Num("1")))), Call("dotProduct", Call("HardinA229693StripTransfer.initial"), Call("Matrix.mulVec", Power(Call("HardinA229693StripTransfer.T"), V("n")), Call("HardinA229693StripTransfer.terminal"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first row contributes the initial weight. Each later row multiplies by the transfer matrix, and terminal weights require exact exhaustion. The empty strip has zero colourings with exactly two defects, whereas the zero-power matrix coefficient counts the positive number of qualifying one-row strips."))), DescribeRole.Theorem))));

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
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula TypeOf(Formula a, Formula b) => Seq(a, Sp, Colon, Sp, b);
    private static Formula Power(Formula a, Formula b) => Seq(Parenthesized(a), Caret, Grp(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
}
