using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferRepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite representative-row quotient certificate.", H("Representative rows"), Blocks(
            Node("representative_rows", "Representative rows", RepresentativeRows(), DescribeRole.Theorem),
            Node("quotient_rows", "Quotient rows", QuotientRows(), DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(title + "."))), role);
    private static Formula RepresentativeRows() => All("i", Fin(D(14)), All("s", Fin(D(14)),
        Eq(Sum("c", Q("Col"), If(And(App(Q("compatible"), App(Q("representatives"), V("i")), V("c")), Eq(App(Q("cls"), V("c")), V("s"))), D(1), D(0))), App(Q("Q"), V("i"), V("s")))));
    private static Formula QuotientRows() => All("b", Q("Col"), All("s", Fin(D(14)),
        Eq(Sum("c", Q("Col"), If(And(App(Q("compatible"), V("b"), V("c")), Eq(App(Q("cls"), V("c")), V("s"))), D(1), D(0))), App(Q("Q"), App(Q("cls"), V("b")), V("s")))));
    private static Formula Sum(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(V("if"), Sp, c, Sp, V("then"), Sp, y, Sp, V("else"), Sp, n));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) => i == 0 ? new[] { Operatorname, Grp(V(part)) } : new[] { Dot, Operatorname, Grp(V(part)) }).ToArray());
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Fin(Formula n) => App(Q("Fin"), n);
}
