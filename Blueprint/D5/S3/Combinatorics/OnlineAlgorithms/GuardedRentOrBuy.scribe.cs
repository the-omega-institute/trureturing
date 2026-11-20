using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OnlineAlgorithms;

internal sealed class GuardedRentOrBuyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/schiavo2026repeatedrentorbuy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A guarded deterministic threshold rule for repeated rent-or-buy.",
        H("The guarded repeated rent-or-buy rule"),
        Blocks(
            Node("State", "State before a new increment is billed", DescribeRole.Definition,
                "The record is presented as an ordered tuple. The real carry is the history left after the previous action. The real "
                + "accumulator is the rent paid since the last reset. The state also stores the optional "
                + "previous increment and two flags for whether an ordinary crossing or a strict drop has occurred."),
            Node("initial", "Initial state", DescribeRole.Definition,
                "Both real entries are zero. The previous increment is absent and both flags are false."),
            Node("crossing", "Ordinary threshold crossing", DescribeRole.Definition,
                "A crossing occurs when the accumulator plus the carry plus the new increment reaches or exceeds the reset price."),
            Node("drop", "Strict decrease in the visible increments", DescribeRole.Definition,
                "A drop occurs if a previous increment exists and the newly visible increment is strictly smaller."),
            Node("reset", "Reset decision", DescribeRole.Definition,
                "Reset at a crossing, or at the first strict drop if an ordinary crossing occurred on an earlier call."),
            Node("advance", "State after the billed call", DescribeRole.Definition,
                "The function choose selects its second argument when its first argument is true, and otherwise its third. "
                + "On a reset, clear the carry and accumulator. Otherwise add the new increment to the carry "
                + "and add that rent to the accumulator. Store the increment and update each flag by disjunction "
                + "with the corresponding test on this call. A simultaneous drop and crossing counts as an ordinary crossing."),
            Node("nextCarry", "Comparator carry after the action", DescribeRole.Definition,
                "The carry is zero after a reset and is the incoming carry plus the visible increment otherwise.", true),
            Node("bill", "Bill on one call", DescribeRole.Definition,
                "Charge incoming carry plus the visible increment on every call. Add the reset price exactly when the action resets.", true),
            Node("comparatorCost", "Cost of a schedule from an incoming carry", DescribeRole.Definition,
                "The empty list has cost zero. For each increment and action pair, add the bill "
                + "and continue from the carry given by that action.", true),
            Node("policyCost", "Cost of the guarded rule from a state", DescribeRole.Definition,
                "The empty list has cost zero. For each increment, add the bill for the rule's reset decision, "
                + "then continue with the updated state."),
            Node("prefixRule", "Horizon-blind decision on a visible prefix", DescribeRole.Definition,
                "The empty prefix chooses no reset. The foldAdvance operation folds advance K over the list. "
                + "For a nonempty prefix, replay every increment before "
                + "its last entry from the initial state. Use the resulting state with the last entry to choose the reset."),
            Node("prefixRule_nil", "The first call does not reset", DescribeRole.Theorem,
                "Call one has no visible increment. Its decision is the value of the prefix rule at the empty list."),
            Node("scheduled", "Increment and decision trace", DescribeRole.Definition,
                "Produce an empty trace on an empty list. Otherwise pair the first increment with the current reset "
                + "decision and compute the remaining trace from the updated state."),
            Node("ordinary_initial", "From the initial state only a crossing resets", DescribeRole.Theorem,
                "The initial state has no previous increment and has never crossed the threshold."),
            Node("scheduled_cost", "The trace has the rule's cost", DescribeRole.Theorem,
                "Induct on the list. Each recursive bill uses the same decision and carry as the rule."),
            Node("scheduled_prefix", "Each recorded decision uses exactly its visible prefix", DescribeRole.Theorem,
                "Induct on the unprocessed list. At the first index the decision is the one computed from the seen prefix "
                + "and the new entry. For a later index, move the head to the seen prefix and advance the fold by that entry."),
            Node("billed_cycle", "Cycle accounting persists through a comparator action", DescribeRole.Theorem,
                "Let e be the rule carry, A its accumulated rent, o the comparator carry and q the comparator's billed cost "
                + "in the unfinished cycle. If the comparator has already paid for the increments and a reset, its next bill "
                + "covers the next increment as well. A comparator reset also establishes that alternative. Otherwise "
                + "the comparator's carry and cost continue to dominate the rule's carried rent and accumulated rent."),
            Node("factor_three", "Factor three against every comparator trace", DescribeRole.Theorem,
                "The rates operation takes the first component of every step. "
                + "At an ordinary crossing, the comparator has paid at least one reset price in that cycle. "
                + "The comparison reserves one reset price after a crossing and spends it at the first later drop "
                + "if that drop forces a reset. The invariant includes unfinished cycles, so it applies when a session "
                + "ends after any bill, including when the comparator cost is zero."))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string explanation,
        bool fromSource = false) => Describe.Lean(
            DescribeId.Create("guarded-rent-or-buy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name),
            H(title),
            StatementSource.FromAuthor(FormulaFor(name)),
            fromSource ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            role);

    private static Formula FormulaFor(string name) => name switch
    {
        "State" => Disp(Seq(
            F.Id("State"), Eq, Seq(Mathbb, Grp(F.Id("R"))), Times, Sp, Seq(Mathbb, Grp(F.Id("R"))), Times, Sp, F.Id("Option"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close, Times, Sp, F.Id("Bool"), Times, Sp, F.Id("Bool"))),
        "initial" => Disp(Seq(
            F.Id("initial"), Eq, Open, D(0), Comma, Sp, D(0), Comma, Sp, F.Id("none"), Comma, Sp,
            F.Id("false"), Comma, Sp, F.Id("false"), Close)),
        "crossing" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("s"), Colon, Sp, F.Id("State"), Close, Comma, Sp, F.Id("crossing"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Leftrightarrow, Sp, F.Id("K"), Le, Sp, F.Id("acc"), Open,
            F.Id("s"), Close, Plus, Open, F.Id("carry"), Open, F.Id("s"), Close, Plus, F.Id("a"), Close)),
        "drop" => Disp(Seq(
            Forall, Sp, Open, F.Id("s"), Colon, Sp, F.Id("State"), Close, Open, F.Id("a"), Colon, Sp,
            Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, F.Id("drop"), Open, F.Id("s"), Comma, Sp, F.Id("a"), Close,
            Leftrightarrow, Sp, Exists, Sp, Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, F.Id("previous"), Open, F.Id("s"), Close, Eq, F.Id("some"), Open, F.Id("p"), Close, Land, Sp, F.Id("a"), Lt, F.Id("p"))),
        "reset" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("s"), Colon, Sp, F.Id("State"), Close, Comma, Sp, F.Id("reset"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Eq, F.Id("decide"), Open, F.Id("crossing"), Open,
            F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Lor, Sp, Open, F.Id("drop"), Open,
            F.Id("s"), Comma, Sp, F.Id("a"), Close, Land, Sp, F.Id("ordinarySeen"), Open, F.Id("s"), Close, Eq,
            F.Id("true"), Land, Sp, F.Id("dropSeen"), Open, F.Id("s"), Close, Eq, F.Id("false"), Close,
            Close)),
        "advance" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("s"), Colon, Sp, F.Id("State"), Close, Comma, Sp, F.Id("advance"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Eq, Open, F.Id("choose"), Open, F.Id("reset"), Open,
            F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Comma, Sp, D(0), Comma, Sp, F.Id("carry"),
            Open, F.Id("s"), Close, Plus, F.Id("a"), Close, Comma, Sp, F.Id("choose"), Open, F.Id("reset"),
            Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Comma, Sp, D(0), Comma, Sp, F.Id("acc"), Open, F.Id("s"), Close, Plus, Open, F.Id("carry"), Open, F.Id("s"), Close,
            Plus, F.Id("a"), Close, Close, Comma, Sp, F.Id("some"), Open, F.Id("a"), Close, Comma, Sp, F.Id("ordinarySeen"), Open, F.Id("s"), Close, Lor, Sp, F.Id("decide"), Open, F.Id("crossing"),
            Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Close, Comma, Sp, F.Id("dropSeen"),
            Open, F.Id("s"), Close, Lor, Sp, F.Id("decide"), Open, F.Id("drop"), Open, F.Id("s"), Comma, Sp, F.Id("a"), Close, Close, Close)),
        "nextCarry" => Disp(Seq(
            Forall, Sp, Open, F.Id("o"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("r"), Colon, Sp, F.Id("Bool"), Close, Comma, Sp, F.Id("nextCarry"), Open, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Eq, F.Id("choose"), Open, F.Id("r"), Comma, Sp, D(0),
            Comma, Sp, F.Id("o"), Plus, F.Id("a"), Close)),
        "bill" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("o"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb,
            Grp(F.Id("R"))), Close,
            Open, F.Id("r"), Colon, Sp, F.Id("Bool"), Close, Comma, Sp, F.Id("bill"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Eq, F.Id("o"), Plus, F.Id("a"), Plus,
            F.Id("choose"), Open, F.Id("r"), Comma, Sp, F.Id("K"), Comma, Sp, D(0), Close)),
        "comparatorCost" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("o"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb,
            Grp(F.Id("R"))), Close,
            Open, F.Id("r"), Colon, Sp, F.Id("Bool"), Close, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open,
            Seq(Mathbb, Grp(F.Id("R"))), Times, Sp, F.Id("Bool"), Close, Close, Comma, Sp, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, OpenBracket,
            CloseBracket, Close, Eq, D(0), Land, Sp, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, F.Id("cons"), Open, Open, F.Id("a"), Comma, Sp, F.Id("r"), Close, Comma, Sp, F.Id("xs"), Close, Close, Eq, F.Id("bill"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Plus, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, F.Id("nextCarry"), Open, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Comma, Sp, F.Id("xs"), Close)),
        "policyCost" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("s"), Colon, Sp, F.Id("State"), Close, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open,
            Seq(Mathbb, Grp(F.Id("R"))), Close, Close, Comma, Sp, F.Id("policyCost"), Open, F.Id("K"),
            Comma, Sp, F.Id("s"), Comma, Sp, OpenBracket, CloseBracket, Close, Eq, D(0), Land, Sp, F.Id("policyCost"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("cons"), Open,
            F.Id("a"), Comma, Sp, F.Id("xs"), Close, Close, Eq, F.Id("bill"), Open, F.Id("K"), Comma, Sp, F.Id("carry"), Open, F.Id("s"), Close, Comma, Sp, F.Id("a"), Comma, Sp, F.Id("reset"), Open,
            F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Close, Plus, F.Id("policyCost"),
            Open, F.Id("K"), Comma, Sp, F.Id("advance"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Comma, Sp, F.Id("xs"), Close)),
        "prefixRule" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("xs"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close, Close, Comma, Sp, F.Id("prefixRule"), Open, F.Id("K"), Comma, Sp, OpenBracket, CloseBracket, Close, Eq,
            F.Id("false"), Land, Sp, F.Id("prefixRule"), Open, F.Id("K"), Comma, Sp, F.Id("append"), Open,
            F.Id("xs"), Comma, Sp, OpenBracket, F.Id("a"), CloseBracket, Close, Close, Eq, F.Id("reset"),
            Open, F.Id("K"), Comma, Sp, F.Id("foldAdvance"), Open, F.Id("K"), Comma, Sp, F.Id("initial"),
            Comma, Sp, F.Id("xs"), Close, Comma, Sp, F.Id("a"), Close)),
        "prefixRule_nil" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, F.Id("prefixRule"), Open, F.Id("K"), Comma, Sp, OpenBracket, CloseBracket, Close, Eq,
            F.Id("false"))),
        "scheduled" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("s"), Colon, Sp, F.Id("State"), Close, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open,
            Seq(Mathbb, Grp(F.Id("R"))), Close, Close, Comma, Sp, F.Id("scheduled"), Open, F.Id("K"),
            Comma, Sp, F.Id("s"), Comma, Sp, OpenBracket, CloseBracket, Close, Eq, OpenBracket, CloseBracket,
            Land, Sp, F.Id("scheduled"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("cons"), Open,
            F.Id("a"), Comma, Sp, F.Id("xs"), Close, Close, Eq, F.Id("cons"), Open, Open, F.Id("a"), Comma, Sp, F.Id("reset"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Close, Comma, Sp, F.Id("scheduled"), Open, F.Id("K"), Comma, Sp, F.Id("advance"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Comma, Sp, F.Id("xs"), Close, Close)),
        "ordinary_initial" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, F.Id("reset"), Open, F.Id("K"), Comma, Sp, F.Id("initial"), Comma, Sp, F.Id("a"), Close, Eq,
            F.Id("decide"), Open, F.Id("crossing"), Open, F.Id("K"), Comma, Sp, F.Id("initial"), Comma, Sp, F.Id("a"), Close, Close)),
        "scheduled_cost" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("s"), Colon, Sp, F.Id("State"), Close, Open, F.Id("xs"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb,
            Grp(F.Id("R"))), Close, Close, Comma, Sp, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, F.Id("carry"), Open, F.Id("s"), Close, Comma, Sp, F.Id("scheduled"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("xs"), Close, Close, Eq, F.Id("policyCost"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("xs"), Close)),
        "scheduled_prefix" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open,
            F.Id("seen"), Sp, F.Id("tail"), Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Close,
            Close, Open, F.Id("i"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Open, F.Id("r"), Colon, Sp, F.Id("Bool"), Close, Comma, Sp, F.Id("getOptional"), Open, F.Id("scheduled"), Open, F.Id("K"),
            Comma, Sp, F.Id("foldAdvance"), Open, F.Id("K"), Comma, Sp, F.Id("initial"), Comma, Sp, F.Id("seen"),
            Close, Comma, Sp, F.Id("tail"), Close, Comma, Sp, F.Id("i"), Close, Eq, F.Id("some"), Open, Open,
            F.Id("a"), Comma, Sp, F.Id("r"), Close, Close, Rightarrow, Sp, F.Id("prefixRule"), Open, F.Id("K"),
            Comma, Sp, F.Id("append"), Open, F.Id("seen"), Comma, Sp, F.Id("take"), Open, F.Id("tail"), Comma, Sp, F.Id("i"), Plus, D(1), Close, Close, Close, Eq, F.Id("r"))),
        "billed_cycle" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("e"), Sp, F.Id("A"), Sp, F.Id("o"), Sp, F.Id("q"),
            Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("r"), Colon, Sp, F.Id("Bool"), Close, Comma, Sp, Open, D(0), Le, Sp, F.Id("K"), Land, Sp, F.Id("e"), Le, Sp, F.Id("A"), Land, Sp, D(0), Le, Sp, F.Id("o"), Land, Sp, Open, F.Id("e"), Plus, F.Id("K"), Le, Sp, F.Id("q"), Lor, Sp, Open, F.Id("A"), Le, Sp, F.Id("q"), Land, Sp, F.Id("e"), Le, Sp, F.Id("o"), Close, Close, Close, Rightarrow, Sp, Open, F.Id("e"), Plus,
            F.Id("a"), Plus, F.Id("K"), Le, Sp, F.Id("q"), Plus, F.Id("bill"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Lor, Sp, Open, F.Id("A"), Plus, Open,
            F.Id("e"), Plus, F.Id("a"), Close, Le, Sp, F.Id("q"), Plus, F.Id("bill"), Open, F.Id("K"),
            Comma, Sp, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"), Close, Land, Sp, F.Id("e"), Plus,
            F.Id("a"), Le, Sp, F.Id("nextCarry"), Open, F.Id("o"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("r"),
            Close, Close, Close)),
        "factor_three" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("steps"),
            Colon, Sp, F.Id("List"), Open, Seq(Mathbb, Grp(F.Id("R"))), Times, Sp, F.Id("Bool"), Close, Close,
            Open, F.Id("first"), Colon, Sp, F.Id("Bool"), Close, Comma, Sp, Open, D(0), Lt, F.Id("K"), Land, Sp, Open, Forall, Sp, Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Times, Sp, F.Id("Bool"),
            Close, Comma, Sp, F.Id("p"), InMacro, Sp, F.Id("steps"), Rightarrow, Sp, F.Id("fst"), Open, F.Id("p"),
            Close, Ge, Sp, D(0), Close, Close, Rightarrow, Sp, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, D(0), Comma, Sp, F.Id("scheduled"), Open, F.Id("K"), Comma, Sp, F.Id("initial"), Comma, Sp, F.Id("rates"), Open, F.Id("steps"), Close, Close, Close, Le, Sp, D(3), Cdot, Sp, Open,
            F.Id("bill"), Open, F.Id("K"), Comma, Sp, D(0), Comma, Sp, D(0), Comma, Sp, F.Id("first"), Close, Plus,
            F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, D(0), Comma, Sp, F.Id("steps"), Close, Close)),
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };
}
