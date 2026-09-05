using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class KernelChainDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classified generator schedules yield disjoint, telescoping escape decompositions.",
        H("Generated-Kernel Chains"),
        Blocks(
            Definition("generator-step-class", "GeneratorStepClass",
                "Generator step classification",
                "Each scheduled addition is certified either as a strict edge or as an extensional stutter."),
            Definition("generator-schedule", "GeneratorSchedule",
                "Generator schedule",
                "A complete bijective ordering records every catalog addition, its node sequence, endpoints, and classification."),
            Definition("strict-kernel-chain", "StrictKernelChain",
                "Strict kernel chain",
                "A stutter-free path retains a strict generator-step certificate at every adjacency."),
            Definition("strict-subsequence", "strictSubsequence",
                "Strict subsequence",
                "Deleting classified stutters produces a strict kernel chain while preserving the path endpoints."),
            Theorem("strict-subsequence-node-zero", "strictSubsequence_node_zero",
                "Strict subsequences preserve the first node", StrictSubsequenceZero()),
            Theorem("strict-subsequence-node-last", "strictSubsequence_node_last",
                "Strict subsequences preserve the terminal node", StrictSubsequenceLast()),
            Theorem("strict-subsequence-added-membership", "strictSubsequence_added_mem",
                "Retained labels come from the schedule", StrictSubsequenceAddedMem()),
            FormulaDescription("schedule-increment-rate", "Schedule increment rate",
                ScheduleIncrementRate(),
                "GeneratorSchedule.incrementRate uses the canonical arena escape denominator."),
            FormulaDescription("strict-chain-increment-rate", "Strict-chain increment rate",
                StrictChainIncrementRate(),
                "StrictKernelChain.incrementRate uses the canonical arena escape denominator."),
            Theorem("collapsed-increment-is-empty", "collapsed_increment_eq_empty",
                "Collapsed increments are empty", CollapsedIncrement()),
            Theorem("chain-increments-pairwise-disjoint", "chain_increment_pairwise_disjoint",
                "Chain increments are pairwise disjoint", PairwiseDisjoint()),
            Theorem("chain-increment-union", "chain_increment_union",
                "Increment union is terminal escape loss", IncrementUnion()),
            Theorem("chain-count-telescopes", "chain_count_telescopes",
                "Increment counts telescope", CountTelescopes()),
            Theorem("chain-rate-telescopes", "chain_rate_telescopes",
                "Increment rates telescope", RateTelescopes()),
            Theorem("strict-chain-terminal-generated-union",
                "strict_chain_terminal_eq_generatedKernel_union",
                "A strict-chain terminal is its generated union", StrictTerminalUnion()),
            Theorem("terminal-order-independent", "terminal_order_independent",
                "Strict-chain terminals are order independent", TerminalIndependent()),
            Theorem("full-schedule-terminal-order-independent",
                "full_schedule_terminal_order_independent",
                "Full-schedule terminals are order independent", FullTerminalIndependent()),
            Theorem("schedule-terminal-is-full-kernel",
                "schedule_terminal_eq_generatedKernel_full",
                "A full schedule ends at the full kernel", TerminalFull()),
            Theorem("last-step-is-unique-capture", "last_step_eq_uniqueCapture",
                "The leave-one-out last step is unique capture", LastUniqueCapture()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The certificate follows from classified generator steps and finite escape-set algebra."))),
            DescribeRole.Theorem);

    private static DocumentBlock.Describe FormulaDescription(
        string id, string title, Formula formula, string paragraph) =>
        Describe.Remark(
            DescribeId.Create(id), H(title), Disp(Seq(formula, Dot)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Schedule() => F.Id("A");
    private static Formula First() => F.Id("A");
    private static Formula Second() => F.Id("B");
    private static Formula R() => F.Id("r");
    private static Formula S() => F.Id("s");
    private static Formula I() => F.Id("i");
    private static Formula Increment(Formula schedule, Formula position) =>
        Call("increment", schedule, position);
    private static Formula Node(Formula schedule, Formula position) =>
        Call("node", schedule, position);
    private static Formula Last(Formula schedule) => Call("last", schedule);
    private static Formula Escape(Formula node) => Call("escapeAt", node);

    private static Formula StrictSubsequenceZero() => Seq(
        Node(Call("strictSubsequence", Schedule()), D(0)), Sp, Eq, Sp,
        Node(Schedule(), D(0)));

    private static Formula StrictSubsequenceLast() => Seq(
        Node(Call("strictSubsequence", Schedule()),
            Last(Call("strictSubsequence", Schedule()))), Sp, Eq, Sp,
        Node(Schedule(), Last(Schedule())));

    private static Formula StrictSubsequenceAddedMem() => Seq(
        Call("added", Call("strictSubsequence", Schedule()), R()), Sp, InMacro, Sp,
        Call("image", Call("added", Schedule()), Call("univ")));

    private static Formula ScheduleIncrementRate() => Seq(
        Call("incrementRate", Schedule(), R()), Sp, Eq, Sp,
        new Formula.Fraction(Call("incrementCount", Schedule(), R()),
            Call("escapeDenominator", F.Id("A"))));

    private static Formula StrictChainIncrementRate() => Seq(
        Call("incrementRate", F.Id("K"), R()), Sp, Eq, Sp,
        new Formula.Fraction(Call("incrementCount", F.Id("K"), R()),
            Call("escapeDenominator", F.Id("A"))));

    private static Formula CollapsedIncrement() => new Formula.Logic(
        Seq(Node(Schedule(), Call("castSucc", R())), Sp, Eq, Sp,
            Node(Schedule(), Call("succ", R()))),
        FormulaLogicOperator.Implies,
        Seq(Increment(Schedule(), R()), Sp, Eq, Sp, Emptyset));

    private static Formula PairwiseDisjoint() => Seq(
        Forall, Sp, R(), Comma, Sp, S(), Comma, Sp,
        R(), Sp, Neq, Sp, S(), Sp, Implies, Sp,
        Call("Disjoint", Increment(Schedule(), R()), Increment(Schedule(), S())));

    private static Formula IncrementUnion() => Seq(
        Call("biUnion", Call("univ"), Call("increment", Schedule())),
        Sp, Eq, Sp,
        Call("sdiff", Escape(Node(Schedule(), D(0))),
            Escape(Node(Schedule(), Last(Schedule())))));

    private static Formula CountTelescopes() => Seq(
        Call("sum", Call("incrementCount", Schedule())), Sp, Plus, Sp,
        Call("card", Escape(Node(Schedule(), Last(Schedule())))),
        Sp, Eq, Sp,
        Call("card", Escape(Node(Schedule(), D(0)))));

    private static Formula RateTelescopes() => Seq(
        Call("sum", Call("incrementRate", Schedule())), Sp, Plus, Sp,
        Call("escapeRate", Node(Schedule(), Last(Schedule()))), Sp, Eq, Sp,
        Call("escapeRate", Node(Schedule(), D(0))));

    private static Formula StrictTerminalUnion() => new Formula.Logic(
        Seq(Node(Schedule(), D(0)), Sp, Eq, Sp,
            Call("generatedKernel", F.Id("C"), F.Id("T"))),
        FormulaLogicOperator.Implies,
        Seq(Node(Schedule(), Last(Schedule())), Sp, Eq, Sp,
            Call("generatedKernel", F.Id("C"),
                Call("union", F.Id("T"), Call("image", Call("added", Schedule()))))));

    private static Formula TerminalIndependent()
    {
        Formula sameStart = new Formula.Logic(
            Seq(Node(First(), D(0)), Sp, Eq, Sp,
                Call("generatedKernel", F.Id("C"), F.Id("T"))),
            FormulaLogicOperator.And,
            Seq(Node(Second(), D(0)), Sp, Eq, Sp,
                Call("generatedKernel", F.Id("C"), F.Id("T"))));
        Formula sameGenerators = Seq(
            Call("image", Call("added", First())), Sp, Eq, Sp,
            Call("image", Call("added", Second())));
        return new Formula.Logic(
            new Formula.Logic(sameStart, FormulaLogicOperator.And, sameGenerators),
            FormulaLogicOperator.Implies,
            FullTerminalIndependent());
    }

    private static Formula FullTerminalIndependent() => Seq(
        Node(First(), Last(First())), Sp, Eq, Sp,
        Node(Second(), Last(Second())));

    private static Formula TerminalFull() => Seq(
        Node(Schedule(), Last(Schedule())), Sp, Eq, Sp,
        Call("generatedKernel", F.Id("C"), Call("fullIndexSet", F.Id("C"))));

    private static Formula LastUniqueCapture()
    {
        Formula premises = new Formula.Logic(
            Call("PositiveLength", Schedule()),
            FormulaLogicOperator.And,
            Seq(Node(Schedule(), Call("penultimate", Schedule())), Sp, Eq, Sp,
                Call("generatedKernel", F.Id("C"), Call("without", F.Id("C"), I()))));
        return new Formula.Logic(
            premises,
            FormulaLogicOperator.Implies,
            Seq(Increment(Schedule(), Call("last", Schedule())), Sp, Eq, Sp,
                Call("uniqueCapturePairs", F.Id("C"), I())));
    }
}
