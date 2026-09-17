using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class EqualityQueryScheduleNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A terminating equality-query protocol that identifies finite candidates admits a "
            + "distinct exhaustive schedule with no greater query count at any target. "
            + "The final candidate is identified without an additional query.",
        H("Equality Query Schedule Normal Form"),
        Blocks(
            Paragraph(Text(
                "An equality query at a center returns true exactly when the target equals "
                    + "that center. Protocols use the canonical PassiveProtocol tree and "
                    + "runPassiveProtocol executor. The scan of an empty or singleton list "
                    + "stops immediately; otherwise it queries the first candidate, stops "
                    + "on true, and scans the remaining list on false. Positions idxOf are "
                    + "zero based, and subtraction in the formulas is natural subtraction.")),
            Describe.Lean(
                DescribeId.Create("scan-identifies-with-exact-depth"),
                DeclarationHandle.Create(Prefix + "scan_identifies_with_exact_depth"),
                H("Identification and the exact stopping count of a schedule"),
                StatementSource.FromAuthor(ScanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the list separates a successful first query from its "
                        + "negative continuation. Distinctness ensures identification. "
                        + "The query count is the one-based position capped at length minus "
                        + "one, so a singleton costs zero and the last two positions of a "
                        + "longer list have the same cost."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equality-protocol-schedule-normal-form"),
                DeclarationHandle.Create(Prefix + "equality_protocol_schedule_normal_form"),
                H("Every identifying tree admits a pointwise faster schedule"),
                StatementSource.FromAuthor(NormalFormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction follows the original tree's negative branch. A center in "
                        + "the candidate set is placed first and removed from the remaining "
                        + "candidates; a center outside the set is discarded. At most one "
                        + "remaining candidate requires no query. The resulting list is "
                        + "distinct and exhaustive, and its stopping count is bounded "
                        + "separately at every target. Consequently every nonnegative "
                        + "weighted sum of stopping counts also weakly decreases."))),
                DescribeRole.Theorem))));

    private static Formula A => F.Id("A");
    private static Formula L => F.Id("L");
    private static Formula S => F.Id("S");
    private static Formula T => F.Id("T");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Scan => Call("scan", L);
    private static Formula Run(Formula tree, Formula x) =>
        Call("runPassiveProtocol", F.Id("equalityReadout"), tree, x);
    private static Formula Depth(Formula tree) => Call("length", Run(tree, X));
    private static Formula Identifies(Formula tree, Formula set) => Seq(
        Forall, Sp, X, Sp, In, Sp, set, Comma, Sp,
        Forall, Sp, Y, Sp, In, Sp, set, Comma, Sp,
        Run(tree, X), Sp, Eq, Sp, Run(tree, Y), Sp, Rightarrow, Sp, X, Sp, Eq, Sp, Y);
    private static Formula Position(Formula size) => Call("min",
        Seq(Call("idxOf", L, X), Sp, Plus, Sp, D(1)),
        Seq(size, Sp, Minus, Sp, D(1)));
    private static Formula Carrier() => Seq(
        Forall, Sp, A, Colon, Sp, Call("Type"), Comma, Sp,
        OpenBracket, Call("DecidableEq", A), CloseBracket, Comma);

    private static Formula ScanFormula() => Disp(new Formula.Aligned([
        Carrier(),
        Seq(Forall, Sp, L, Colon, Sp, Call("List", A), Comma, Sp,
            Call("Nodup", L), Sp, Rightarrow),
        Seq(Open, Identifies(Scan, L), Close, Sp, Land),
        Seq(Open, Forall, Sp, X, Sp, In, Sp, L, Comma, Sp,
            Depth(Scan), Sp, Eq, Sp, Position(Call("length", L)), Close, Dot)
    ]));

    private static Formula NormalFormFormula() => Disp(new Formula.Aligned([
        Carrier(),
        Seq(Forall, Sp, T, Colon, Sp,
            Call("PassiveProtocol", A, Seq(Open, Underscore, Sp, Mapsto, Sp,
                Call("Bool"), Close)), Comma, Sp,
            S, Colon, Sp, Call("Finset", A), Comma),
        Seq(Open, Identifies(T, S), Close, Sp, Rightarrow),
        Seq(Exists, Sp, L, Colon, Sp, Call("List", A), Comma, Sp,
            Call("Nodup", L), Sp, Land, Sp, Call("toFinset", L), Sp, Eq, Sp, S, Sp, Land),
        Seq(Open, Identifies(Scan, S), Close, Sp, Land),
        Seq(Open, Forall, Sp, X, Sp, In, Sp, S, Comma, Sp,
            Depth(Scan), Sp, Eq, Sp, Position(Call("card", S)), Close, Sp, Land),
        Seq(Open, Forall, Sp, X, Sp, In, Sp, S, Comma, Sp,
            Depth(Scan), Sp, Leq, Sp, Depth(T), Close, Dot)
    ]));
}
