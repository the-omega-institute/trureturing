using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7;
internal sealed class HardinA229585StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("type-row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Rows"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.Row"), Arrow(Call("Fin", Num("7")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row lists its colours in column order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("type-boundary"),
                DeclarationHandle.Create(Prefix + "Boundary"), H("Outgoing boundary"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.Boundary"), Arrow(Call("Fin", Num("6")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The tail of a row meets the following row along antidiagonal bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("Horizontal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.horizontal"), Call("Finset.image", Fn("j", Call("Fin", Num("6")), Pair(Call("Fin.castSucc", V("j")), Call("Fin.succ", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antidiagonal"),
                DeclarationHandle.Create(Prefix + "antidiagonal"), H("Antidiagonal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.antidiagonal"), Call("Finset.image", Fn("j", Call("Fin", Num("6")), Pair(Call("Fin.succ", V("j")), Call("Fin.castSucc", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boundary"),
                DeclarationHandle.Create(Prefix + "boundary"), H("Retaining the outgoing tail"),
                StatementSource.FromAuthor(Disp(All("r", V("Row"), Eq(Call("HardinA229585StripData.boundary", V("r")), Call("Fin.tail", V("r")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Column zero does not meet the next row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cross"),
                DeclarationHandle.Create(Prefix + "cross"), H("Defects between rows"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("r", V("Row"), Eq(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.antidiagonal"), Call("Fin.cons", Num("0"), V("p")), V("r"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inserted zero is outside every antidiagonal bond."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Admissible residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Iff(Call("HardinA229585StripData.Valid", V("p"), V("d")), And(Leq(V("d"), Num("1")), Leq(Call("Finset.card", Call("Finset.filter", Fn("j", Call("Fin", Num("5")), Eq(App(V("p"), Call("Fin.castSucc", V("j"))), App(V("p"), Call("Fin.succ", V("j"))))), Call("Finset.univ"))), Sub(Num("1"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-budget-class"),
                DeclarationHandle.Create(Prefix + "zeroBudgetClass"), H("Zero-budget class injection"),
                StatementSource.FromAuthor(Disp(Seq(Call("HardinA229585StripData.zeroBudgetClass"), Colon, Sp,
                    Arrow(Call("Fin", Num("16")), Call("Fin", Num("72")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This injection places the sixteen proper-boundary classes in the "
                    + "zero-budget part of the 72-class ordering. The classifier cl, the delegated "
                    + "zero-budget transfer block, and the owner-generated successor multisets all use "
                    + "this ordering."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Colour permutation classes"),
                StatementSource.FromAuthor(Disp(Seq(Call("HardinA229585StripData.cl"), Colon, Sp,
                    Arrow(V("Boundary"), Arrow(V("Nat"), Call("Fin", Num("72"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Proper boundaries use HardinA233255ShapeSymmetry.classOf and "
                    + "its representatives/shapeEquiv ordering. Budget one includes its value in "
                    + "Fin 72; every other budget composes classOf with zeroBudgetClass. Nonproper "
                    + "inputs use the equality classifier in the Lean definition, including its "
                    + "invalid-budget behaviour."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Class transfer matrix"),
                StatementSource.FromAuthor(Disp(Seq(Call("HardinA229585StripData.T"), Colon, Sp, Call("Matrix", Call("Fin", Num("72")), Call("Fin", Num("72")), V("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This 72 by 72 integer matrix uses source and destination indices in Fin 72, in "
                    + "cl order. Its leading 16 by 16 block is HardinA233255Recurrence.table through "
                    + "the inclusion i ↦ i. The zero-budget block uses the same owner table through "
                    + "zeroBudgetClass on both indices, with zero entries outside that column image in "
                    + "its rows. The other entries remain the literal transition weights in the Lean "
                    + "owner. HardinA233255Recurrence.table_matches pins the delegated table to K. "
                    + "HardinA229585StripOrbitTable.table_counts pins every T entry to the count of "
                    + "the destination class in images, and "
                    + "HardinA229585StripOrbitCertificate.transition_counts identifies those "
                    + "multiplicities with actual permitted rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("Initial labelled row counts"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.initial"), Vector(Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("6"), Num("12"), Num("6"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("6"), Num("12"), Num("6"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors are displayed in index order using Lean vector notation ![...]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Terminal acceptance weights"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripData.terminal"), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors are displayed in index order using Lean vector notation ![...]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("Forward transfer table"),
                StatementSource.FromAuthor(Disp(Seq(Call("HardinA229585StripData.W"), Colon, Sp, Arrow(Call("Fin", Num("11")), Arrow(Call("Fin", Num("72")), V("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The eleven integer vectors are indexed by Fin 11; each has 72 coordinates in cl "
                    + "order. The first vector is initial; the remaining ten are the finite row vectors in the Lean definition. "
                    + "HardinA229585StripCertificate.structural_certificate pins W 0 to initial, each "
                    + "of the ten following vectors to Matrix.vecMul of its predecessor with T, and W "
                    + "10 to the stated linear combination of W 2 through W 9. The five "
                    + "ForwardChecks.forward_steps theorems check those ten successive transfer steps."))), DescribeRole.Definition))));

    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

}
