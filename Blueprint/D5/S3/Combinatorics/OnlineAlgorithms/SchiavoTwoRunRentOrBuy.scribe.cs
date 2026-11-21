using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OnlineAlgorithms;

internal sealed class SchiavoTwoRunRentOrBuyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/schiavo2026repeatedrentorbuy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One online rule with factor three and a two-run additive bound.",
        H("Schiavo's two-run question for repeated rent-or-buy"),
        Blocks(
            Model("AtMostTwoRuns", "At most two constant runs",
                "The increment list is the concatenation of two lists, each a replication of a real rate "
                + "for a natural number of entries. Empty blocks and equal rates are allowed."),
            Model("sessionCost", "Cost on the whole session",
                "Add the first-call bill, with zero history and no new increment, to the cost of the "
                + "paired list from zero carry. A comparator has one freely chosen first action and one "
                + "action per increment. The length hypothesis in the theorem pairs every increment."),
            Model("actions", "Actions obtained from visible prefixes",
                "For each zero-based index i of the increment list, evaluate the rule on its first i+1 "
                + "increments. The separate first action uses the empty list."),
            Describe.Lean(
                DescribeId.Create("schiavo-section-five-b-third-question"),
                DeclarationHandle.Create(Module + ".schiavo_section5b_third_question"),
                H("One deterministic rule achieves both bounds"),
                StatementSource.FromAuthor(FormulaFor("schiavo_section5b_third_question")),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In the third question of §5.B (arXiv:2611.06955v1, PDF page 15), "
                        + "Schiavo asks, “Can a rule lose at most 2K on two runs "
                        + "and also be c-competitive for some constant c?”")),
                    Paragraph(Text("Take c = 3. For every positive real reset price K, choose the guarded "
                        + "prefix rule once. On every finite list of nonnegative real increments, "
                        + "and against every comparator schedule of the same horizon, its cost is at most "
                        + "three times the comparator cost. If the increment list has at most two runs, "
                        + "its cost is also at most the comparator cost plus 2K.")),
                    Paragraph(Text("The list has length T−1. Call t observes the first t−1 entries, "
                        + "and every call, including the final call and each reset call, pays the full "
                        + "incoming history as rent. Both inequalities hold for the same deterministic "
                        + "rule. The arbitrary comparator includes any minimum-cost schedule.")),
                    Paragraph(Text("The replayed decisions agree with the evaluations on visible "
                        + "prefixes. The competitive inequality follows from cycle accounting, and the "
                        + "additive inequality follows from the two constant-block comparison. The "
                        + "empty increment list represents a one-call session."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("schiavo-2026-two-run-rent-or-buy"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Model(string name, string title, string explanation) =>
        Describe.Lean(
            DescribeId.Create("schiavo-two-runs-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name),
            H(title),
            StatementSource.FromAuthor(FormulaFor(name)),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));

    private static Formula FormulaFor(string name) => name switch
    {
        "AtMostTwoRuns" => Disp(Seq(
            Forall, Sp, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close,
            Close, Comma, Sp, F.Id("AtMostTwoRuns"), Open, F.Id("xs"), Close, Leftrightarrow, Sp, Exists, Sp, Open,
            F.Id("a"), Sp, F.Id("b"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("m"), Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, F.Id("xs"), Eq,
            Name("List"), Dot, Name("replicate"), Open, F.Id("m"), Comma, Sp, F.Id("a"), Close, Sp, Plus, Plus, Sp,
            Name("List"), Dot, Name("replicate"), Open, F.Id("n"), Comma, Sp, F.Id("b"), Close)),
        "sessionCost" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("xs"),
            Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close, Close, Open, F.Id("first"),
            Colon, Sp, F.Id("Bool"), Close, Open, F.Id("rs"), Colon, Sp, F.Id("List"), Open, F.Id("Bool"),
            Close, Close, Comma, Sp, F.Id("sessionCost"), Open, F.Id("K"), Comma, Sp, F.Id("xs"), Comma, Sp, F.Id("first"), Comma, Sp, F.Id("rs"), Close, Eq, F.Id("bill"), Open, F.Id("K"), Comma, Sp, D(0),
            Comma, Sp, D(0), Comma, Sp, F.Id("first"), Close, Plus, F.Id("comparatorCost"), Open, F.Id("K"),
            Comma, Sp, D(0), Comma, Sp, F.Id("xs"), Dot, Name("zip"), Open, F.Id("rs"), Close, Close)),
        "actions" => Disp(Seq(
            Forall, Sp, Open, F.Id("rule"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close,
            Rightarrow, Sp, F.Id("Bool"), Close, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb,
            Grp(F.Id("R"))), Close, Close, Comma, Sp, F.Id("actions"), Open, F.Id("rule"), Comma, Sp, F.Id("xs"), Close, Eq,
            Name("List"), Dot, Name("ofFn"), Open, Open, F.Id("i"), Colon, Sp, Name("Fin"), Open,
            F.Id("xs"), Dot, Name("length"), Close, Close, Mapsto, Sp,
            F.Id("rule"), Open, F.Id("xs"), Dot, Name("take"),
            Open, F.Id("i"), Dot, Name("val"), Plus, D(1), Close, Close, Close)),
        "schiavo_section5b_third_question" => Disp(Seq(
            Exists, Sp, Open, F.Id("c"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, D(1), Le, Sp, F.Id("c"), Land, Sp, Open, Forall, Sp, Open, F.Id("K"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close,
            Comma, Sp, D(0), Lt, F.Id("K"), Rightarrow, Sp, Exists, Sp, Open, F.Id("rule"), Colon, Sp, F.Id("List"),
            Open, Seq(Mathbb, Grp(F.Id("R"))), Close, Rightarrow, Sp, F.Id("Bool"), Close, Comma, Sp, Forall, Sp, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close, Close,
            Comma, Sp, Open, Forall, Sp, Open, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, F.Id("a"), InMacro, Sp, F.Id("xs"), Rightarrow, Sp, D(0), Le, Sp, F.Id("a"), Close, Rightarrow, Sp, Forall, Sp, Open, F.Id("first"), Colon, Sp, F.Id("Bool"), Close, Open, F.Id("rs"), Colon, Sp, F.Id("List"),
            Open, F.Id("Bool"), Close, Close, Comma, Sp, F.Id("rs"), Dot, Name("length"), Eq,
            F.Id("xs"), Dot, Name("length"), Rightarrow, Sp,
            Name("let"), Sp, Name("online"), Sp, Colon, Eq, Sp,
            Name("sessionCost"), Open, F.Id("K"), Comma, Sp, F.Id("xs"), Comma, Sp,
            F.Id("rule"), Open, OpenBracket, CloseBracket, Close, Comma, Sp,
            Name("actions"), Open, F.Id("rule"), Comma, Sp, F.Id("xs"), Close, Close, Semi, Sp,
            Name("let"), Sp, Name("offline"), Sp, Colon, Eq, Sp,
            Name("sessionCost"), Open, F.Id("K"), Comma, Sp, F.Id("xs"), Comma, Sp, F.Id("first"),
            Comma, Sp, F.Id("rs"), Close, Semi, Sp,
            Open, Name("online"), Le, Sp, F.Id("c"), Cdot, Sp, Name("offline"), Land, Sp,
            Open, Name("AtMostTwoRuns"), Open, F.Id("xs"), Close, Rightarrow, Sp,
            Name("online"), Le, Sp, Name("offline"), Plus, D(2), Cdot, Sp, F.Id("K"), Close, Close, Close)),
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };
}
