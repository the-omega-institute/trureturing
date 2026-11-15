using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229583StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229583";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("type-row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Rows"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.Row"), Arrow(Call("Fin", Num("5")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row lists its colours in column order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("type-boundary"),
                DeclarationHandle.Create(Prefix + "Boundary"), H("Outgoing boundary"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.Boundary"), Arrow(Call("Fin", Num("4")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The tail of a row meets the following row along antidiagonal bonds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("Horizontal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.horizontal"), Call("Finset.image", Fn("j", Call("Fin", Num("4")), Pair(Call("Fin.castSucc", V("j")), Call("Fin.succ", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antidiagonal"),
                DeclarationHandle.Create(Prefix + "antidiagonal"), H("Antidiagonal bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.antidiagonal"), Call("Finset.image", Fn("j", Call("Fin", Num("4")), Pair(Call("Fin.succ", V("j")), Call("Fin.castSucc", V("j")))), Call("Finset.univ"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each index specifies one bond, and each bond is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boundary"),
                DeclarationHandle.Create(Prefix + "boundary"), H("Retaining the outgoing tail"),
                StatementSource.FromAuthor(Disp(All("r", V("Row"), Eq(Call("HardinA229583StripData.boundary", V("r")), Call("Fin.tail", V("r")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Column zero does not meet the next row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cross"),
                DeclarationHandle.Create(Prefix + "cross"), H("Defects between rows"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("r", V("Row"), Eq(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.antidiagonal"), Call("Fin.cons", Num("0"), V("p")), V("r"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inserted zero is outside every antidiagonal bond."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Admissible residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Iff(Call("HardinA229583StripData.Valid", V("p"), V("d")), And(Leq(V("d"), Num("1")), Leq(Call("Finset.card", Call("Finset.filter", Fn("j", Call("Fin", Num("3")), Eq(App(V("p"), Call("Fin.castSucc", V("j"))), App(V("p"), Call("Fin.succ", V("j"))))), Call("Finset.univ"))), Sub(Num("1"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Colour permutation classes"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", V("Nat"), Eq(Call("HardinA229583StripData.cl", V("p"), V("d")), Conditional(And(Eq(V("d"), Num("1")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("0"), Conditional(And(Eq(V("d"), Num("1")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("1"), Conditional(And(Eq(V("d"), Num("1")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("2"), Conditional(And(Eq(V("d"), Num("1")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("3"), Conditional(And(Eq(V("d"), Num("0")), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("4"), Conditional(And(Eq(V("d"), Num("0")), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("5"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Eq(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("6"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("7"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("8"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("9"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("10"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("11"), Conditional(And(Eq(V("d"), Num("0")), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("1"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("2"))), And(Ne(App(V("p"), Num("0")), App(V("p"), Num("3"))), And(Ne(App(V("p"), Num("1")), App(V("p"), Num("2"))), And(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Ne(App(V("p"), Num("2")), App(V("p"), Num("3"))))))))), Num("12"), Num("13"))))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Only equality relations between boundary colours affect continuation counts. The classes also record the remaining defect budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Class transfer matrix"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.T"), Vector(Vector(Num("5"), Num("5"), Num("3"), Num("3"), Num("1"), Num("1"), Num("5"), Num("3"), Num("3"), Num("2"), Num("2"), Num("5"), Num("5"), Num("3")), Vector(Num("4"), Num("4"), Num("3"), Num("3"), Num("2"), Num("2"), Num("4"), Num("2"), Num("2"), Num("3"), Num("3"), Num("6"), Num("6"), Num("3")), Vector(Num("2"), Num("2"), Num("3"), Num("3"), Num("4"), Num("4"), Num("2"), Num("7"), Num("7"), Num("3"), Num("3"), Num("6"), Num("6"), Num("3")), Vector(Num("4"), Num("4"), Num("3"), Num("3"), Num("2"), Num("2"), Num("4"), Num("6"), Num("6"), Num("1"), Num("1"), Num("4"), Num("4"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("5"), Num("5"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("Initial labelled row counts"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.initial"), Vector(Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Terminal acceptance weights"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.terminal"), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("Forward transfer table"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229583StripData.W"), Vector(Vector(Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12")), Vector(Num("180"), Num("180"), Num("144"), Num("144"), Num("108"), Num("108"), Num("180"), Num("438"), Num("438"), Num("108"), Num("108"), Num("516"), Num("516"), Num("144")), Vector(Num("2484"), Num("2484"), Num("1944"), Num("1944"), Num("1404"), Num("1404"), Num("2484"), Num("11142"), Num("11142"), Num("1476"), Num("1476"), Num("11232"), Num("11232"), Num("1944")), Vector(Num("34020"), Num("34020"), Num("26568"), Num("26568"), Num("19116"), Num("19116"), Num("34020"), Num("223182"), Num("223182"), Num("20196"), Num("20196"), Num("209304"), Num("209304"), Num("26568")), Vector(Num("465588"), Num("465588"), Num("363528"), Num("363528"), Num("261468"), Num("261468"), Num("465588"), Num("4023270"), Num("4023270"), Num("276372"), Num("276372"), Num("3621672"), Num("3621672"), Num("363528")), Vector(Num("6371460"), Num("6371460"), Num("4974696"), Num("4974696"), Num("3577932"), Num("3577932"), Num("6371460"), Num("68322366"), Num("68322366"), Num("3782052"), Num("3782052"), Num("59919912"), Num("59919912"), Num("4974696")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order."))), DescribeRole.Definition))));

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
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}
