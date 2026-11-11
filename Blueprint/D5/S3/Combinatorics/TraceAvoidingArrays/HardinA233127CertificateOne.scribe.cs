using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127CertificateOneDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233127");
    private static Formula Seen() => Name(
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen");
    private static Formula PairRow() => Name(
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Boundary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact square-strip transitions by first boundary label.",
        H("Scanner fibres and boundary certificates"), Blocks(
            Describe.Lean(DescribeId.Create("rows"), DeclarationHandle.Create(
                "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne.row_counts_one"),
                H("The first label is 1"), StatementSource.FromAuthor(Disp(RowCounts())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The theorem D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233127SquareStrip.row_counts_one certifies all valid "
                    + "boundaries with the indicated first label. The final row_counts "
                    + "interface consumes it when combining the three first-label cases."))),
                DescribeRole.Theorem))));

    private static Formula RowCounts()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return All("s", Seen(), All("p", PairRow(), Imp(Call(Root + "Valid", s, p),
            Imp(Eq(At(p, Typed(D(0), Fin(6))), Typed(D(1), Fin(3))),
            All("k", Fin(11), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k)))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((p, i) =>
        (i == 0 ? Array.Empty<Formula>() : new Formula[] { Dot }).Append(
            Seq(Operatorname, Grp(p.Select((c, j) => c >= '0' && c <= '9'
                ? D((byte)(c - '0')) : V(p.Substring(j, 1))).ToArray())))).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Numeral(byte k) => k switch
    {
        10 => D(1,0),
        11 => D(1,1),
        _ => D(k)
    };
    private static Formula Fin(byte k) => Call("Fin", Numeral(k));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));

}
