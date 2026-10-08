using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual history data from original controller histories.",
        H("StationaryHistoryData"),
        Blocks(
            Result("actual_history_data", "actual-history-data", "Derived actual history data",
                InitializedScope(Call("HistoryData", V("C"), V("hP"), V("I"))),
                "HistoryData derives positive bounded read counts, exact first events, "
                + "event levels, times and colors, nonempty supports, parent levels and "
                + "support inclusion, and disjoint indexed event fibers. Event and history-label "
                + "incidence are equivalent. The exact root and leaf cardinalities are three "
                + "and 3P. Every graph leaf has the fixed original output of each supporting "
                + "input. Root colors, shifts and levels are c, ell and zero, with the exact "
                + "first-digit supports. Same-control phase supports are disjoint, time is "
                + "shift plus level, and every successive read has a positive literal wait "
                + "equal to its shift increase. Singleton continuations have one child. "
                + "All these fields are obtained from C and I; interval propagation and "
                + "binary-node counts are not fields of HistoryData."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Scope(Formula body) => All("P", N,
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        All("C", Call("Controller", V("P"), V("Q")), All("hP", LT(D(1), V("P")), body))));
    private static Formula InitializedScope(Formula body) => Scope(All("ell", N, All("h", N,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")),
            Seq(OpenBracket, Call("NeZero", Seq(D(3), Times, Sp, V("P"))), CloseBracket, body)))));
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryData", declaration, id, title, statement, explanation);
}
