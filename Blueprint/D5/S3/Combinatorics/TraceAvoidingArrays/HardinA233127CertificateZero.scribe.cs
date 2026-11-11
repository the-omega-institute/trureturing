using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127CertificateZeroDocument : IScribeDocumentDefinition
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
            Describe.Lean(DescribeId.Create("fibres"), DeclarationHandle.Create(
                "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.class_fibres_normalized"),
                H("The six-coordinate scanner-fibre sum"), StatementSource.FromAuthor(Disp(Fibres())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The theorem D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233127SquareStrip.class_fibres_normalized replaces individual "
                    + "colour rows by their exact scanner fibres. Its public interface is "
                    + "used by the private boundary proofs in all three certificate modules."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rows"), DeclarationHandle.Create(
                "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.row_counts_zero"),
                H("The first label is 0"), StatementSource.FromAuthor(Disp(RowCounts())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The theorem D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233127SquareStrip.row_counts_zero certifies all valid "
                    + "boundaries with the indicated first label. The final row_counts "
                    + "interface consumes it when combining the three first-label cases."))),
                DescribeRole.Theorem))));

    private static Formula RowCounts()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return All("s", Seen(), All("p", PairRow(), Imp(Call(Root + "Valid", s, p),
            Imp(Eq(At(p, Typed(D(0), Fin(6))), Typed(D(0), Fin(3))),
            All("k", Fin(11), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k)))))));
    }

    private static Formula Fibres()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        var q = Vector(V("q0"), V("q1"), V("q2"), V("q3"), V("q4"), V("q5"));
        var j = V("j");
        var adjacent = All("j", Fin(5), Ne(At(q, Call("Fin.castSucc", j)),
            At(q, Call("Fin.succ", j))));
        var compatible = All("j", Fin(6), Ne(At(p, j), At(q, j)));
        var finished = Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233255LiteralBridge.rowFinish", s, q);
        var weight = Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233255LiteralBridge.rowWeight", s, q);
        Formula sum = Mul(weight, Conditional(And(adjacent, And(compatible,
            Eq(Call(Root + "boundaryClass", finished, q), k))), D(1), D(0)));
        for (var i = 5; i >= 0; i--) sum = SumOver("q" + i, Fin(3), sum);
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(11),
            Eq(Call(Root + "classCount", s, p, k), sum))));
    }

    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
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
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Conditional(Formula test, Formula yes, Formula no) =>
        Parenthesized(Seq(Name("if"), Sp, Parenthesized(test), Sp, Name("then"), Sp,
            Parenthesized(yes), Sp, Name("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));

}
