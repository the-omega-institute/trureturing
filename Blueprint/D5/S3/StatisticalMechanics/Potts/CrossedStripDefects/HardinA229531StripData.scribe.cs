using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229531StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229531";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-five HDA transfer.", H("Width-five HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("inherited-transitions"),
                DeclarationHandle.Create(Prefix + "raw_successors"),
                H("Proper successors from the frozen scanner certificate"), StatementSource.FromAuthor(Disp(RawSuccessorsFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every proper source row and every Fin 7 target class, thirty-two times the raw proper successor sum equals the corresponding frozen transfer entry. The proof applies the original class_fibres and finite_certificate and pushes saturated Seen fibres with weight 32. Each consumed target-class theorem supplies its own exact bond, budget and class correspondence before integer division."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row"), DeclarationHandle.Create(Prefix + "Row"),
                H("Actual rows"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229531StripData.Row"), RowType()))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Row is the function type Fin 5 to Fin 3. Its 243 values are the actual labelled rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"), DeclarationHandle.Create(Prefix + "horizontal"),
                H("Horizontal bonds"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229531StripData.horizontal"), Call("HardinA229583StripData.horizontal")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The horizontal bond set is HardinA229583StripData.horizontal, containing the four adjacent pairs in Fin 5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("between"), DeclarationHandle.Create(Prefix + "between"),
                H("Crossed bonds"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229531StripData.between"), Seq(Call("HardinA229583StripData.antidiagonal"), Sp, Cup, Sp, Call("Finset.image", Call("Prod.swap"), Call("HardinA229583StripData.antidiagonal")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inter-row bond set is the union of HardinA229583StripData.antidiagonal with its coordinate-swapped image, containing both diagonals for each adjacent column pair."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Valid residual states"), StatementSource.FromAuthor(Disp(All("p", RowType(), All("d", Call("Nat"), Eq(Call("HardinA229531StripData.Valid", V("p"), V("d")), Parenthesized(And(Le(V("d"), Num("1")), Le(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), V("p"), V("p")), Sub(Num("1"), V("d")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Valid p d means that d is at most one and the internal horizontal defect count of p is at most one minus d."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidablevalid"), DeclarationHandle.Create(Prefix + "decidableValid"),
                H("Finite state decision"), StatementSource.FromAuthor(Disp(All("p", RowType(), All("d", Call("Nat"), Typed(Call("HardinA229531StripData.decidableValid", V("p"), V("d")), Call("Decidable", Call("HardinA229531StripData.Valid", V("p"), V("d")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The instance decides the conjunction defining Valid on an actual row and natural residual budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("The class map"), StatementSource.FromAuthor(Disp(ClassFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The map Row times Nat to Fin 20 identifies global colour permutations and reflection. Proper rows use HardinA233126SquareStrip.boundaryClass at Seen=(true,true); defective rows use their full equality pattern. The transition_counts theorems pin the class transfer for every valid state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("The transfer matrix"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229531StripData.T"), Call("Matrix", Fin(20), Fin(20), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("T is an integer matrix indexed by Fin 20 on both axes. Its proper-row diagonal subblocks call HardinA233171DiagonalStrip.transfer at indices one through six and divide by 32. The division removes the two lifts per colour in each of five cells after Seen is saturated. Every entry is pinned to the actual three-colour successor sum by HardinA229531StripClasses.transition_counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Initial distribution"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229531StripData.initial"), Arrow(Fin(20), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The vector Fin 20 to Int counts first rows by their exact residual budget and class. HardinA229531Strip.finite_certificate verifies these weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("Terminal acceptance"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229531StripData.terminal"), Arrow(Fin(20), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The vector Fin 20 to Int is one exactly at zero-residual classes and zero otherwise; HardinA229531Strip.finite_certificate checks this for all valid rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("Forward weights"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229531StripData.W"), Arrow(Fin(14), Arrow(Fin(20), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("W has type Fin 14 to Fin 20 to Int. Its fourteen rows are the initial vector followed by thirteen right multiplications by T. HardinA229531Strip.finite_certificate pins those identities and the order-twelve polynomial relation."))), DescribeRole.Definition))));
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

    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));



    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula RowType() => Arrow(Fin(5), Fin(3));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));


    private static Formula ClassFormula()
    {
        var p = V("p"); var d = V("d");
        return All("p", RowType(), All("d", Call("Nat"), Eq(Typed(Call("HardinA229531StripData.cl", p, d), Fin(20)),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("1")))), Num("0"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("2")))), Num("1"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("3")))), Num("2"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("4")))), Num("3"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("5")))), Num("4"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("6")))), Num("5"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("1")))), Num("6"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("2")))), Num("7"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("3")))), Num("8"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("4")))), Num("9"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("5")))), Num("10"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), p, p), Num("0")), Eq(Call("HardinA233126SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), p), Num("6")))), Num("11"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Eq(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Eq(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Eq(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Eq(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Eq(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("12"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Eq(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Eq(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Eq(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("13"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Eq(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Eq(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Eq(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("14"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Eq(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Eq(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Eq(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("15"),
            Conditional(And(Eq(d, Num("0")), Or(And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Eq(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Eq(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Eq(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Eq(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("16"),
            Conditional(And(Eq(d, Num("0")), Or(And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Eq(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Eq(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Eq(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Eq(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("17"),
            Conditional(And(Eq(d, Num("0")), Or(And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Eq(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("4"))), And(Ne(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("0")), App(p, Num("4"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("4"))), And(Eq(App(p, Num("2")), App(p, Num("3"))), And(Ne(App(p, Num("2")), App(p, Num("4"))), Ne(App(p, Num("3")), App(p, Num("4")))))))))))))), Num("18"),
            Num("19")))))))))))))))))))))));
    }

    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));

    private static Formula RawSuccessorsFormula()
    {
        var p = V("p"); var q = V("q"); var j = V("j");
        var seen = Pair(Call("true"), Call("true"));
        Formula Class(Formula row) => Call("HardinA233126SquareStrip.boundaryClass", seen, row);
        var indicator = Typed(Conditional(And(Call("HardinThinGraphTransport.proper", q),
            And(Call("HardinThinGraphTransport.compatible", Call("true"), p, q), Eq(Class(q), j))), Num("1"), Num("0")), Call("Int"));
        return All("p", RowType(), Imp(Call("HardinThinGraphTransport.proper", p), All("j", Fin(7),
            Eq(Mul(Num("32"), Parenthesized(SumOver("q", RowType(), indicator))),
                Call("HardinA233171DiagonalStrip.transfer", Class(p), j)))));
    }

}
