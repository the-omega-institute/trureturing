using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class InitialTailCostDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InitialTailCost.";

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var k = F.Id("k"); var m = F.Id("m"); var n = F.Id("n");
        var alphabet = F.Id("alphabet"); var controller = F.Id("controller");
        var history = F.Id("history");
        var record = Call("historyRecord", history);
        var treeType = Call("AcquisitionTree", k, m, alphabet, Call("Option", nat), n);
        var controllerType = Arrow(Call("Option", Call("ZMod", D(2))), treeType);
        var historyType = Call("List", Call("AllowedBlock", k, m, alphabet));
        var correct = Equal(
            Call("result", Apply(controller, Call("endpointReading", record)), record),
            Call("map", Seq(Operatorname, Grp(F.Id("tail"))), record));
        var feasible = Exists("controller", controllerType, All("history", historyType, correct));
        var budgets = Or(And(Equal(m, D(1)), Le(Subtract(k, D(1)), n)),
            And(Equal(k, D(2)), Le(D(1), n)));
        var statement = All("k", nat, All("m", nat,
            Imp(And(Le(D(2), k), Le(D(1), m)),
                All("alphabet", F.Id("Bool"), All("n", nat, Iff(feasible, budgets))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact initial-tail budgets on all actual complete-block histories.",
            H("Initial tail acquisition and sharp block cost"),
            Blocks(Describe.Lean(
                DescribeId.Create("initial-tail-budget-exact"),
                DeclarationHandle.Create(Owner + "initial_tail_budget_exact"),
                H("Every feasible budget for the complete initial tail"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every original order k>=2 and width m>=1, alphabet=false "
                        + "allows every binary block, while alphabet=true allows blocks "
                        + "with no internal run of k ones. Each history is any finite "
                        + "sequence in the selected alphabet, including the empty history "
                        + "and histories that have rejected. historyRecord is generated "
                        + "from the empty word by literal chronological bit updates, "
                        + "using the original KBonacci weights and fixed mod-two reading. "
                        + "The target is its initial tail: some(s) for a live initial "
                        + "record and none for an initially rejected record.")),
                    Paragraph(Text(
                        "The controller receives the initial endpoint output for free. "
                        + "Its finite tree has uniform horizon n; each step issues exactly "
                        + "one full block and follows the attained endpoint reply. "
                        + "No internal bit output, reset, copy, initial phase clock or "
                        + "unexecuted branch is provided. The label refers to the initial "
                        + "history even when an issued block changes or rejects it. "
                        + "Actual joint realization supplies every live value-phase-tail "
                        + "record in SourceRecord and the absorbing rejected record.")),
                    Paragraph(Text(
                        "Thus the full initial tail is acquired exactly when m=1 or k=2. "
                        + "For m=1 the least worst-case number of additional blocks is "
                        + "k-1. Sequential ones label a first rejection at step r by "
                        + "initial tail k-r; after k-1 successes the initial tail is zero. "
                        + "Same-value, same-phase adjacent tails zero and one have the "
                        + "same outputs before step k-1, and any earlier zero merges "
                        + "their records. Induction over arbitrary adaptive trees yields "
                        + "the lower bound.")),
                    Paragraph(Text(
                        "For k=2 and every positive width, a leading one followed by "
                        + "zeros rejects initial tail one and preserves initial tail "
                        + "zero, so the least worst-case cost is one block. A zero-block "
                        + "tree cannot distinguish the two same-value actual tails. "
                        + "For k>=3 and m>=2, the first-zero criterion rules out the "
                        + "full tail target: clearing merges at least two survivors or "
                        + "rejection merges at least two distinct tails. The all-one "
                        + "branch also merges at least two rejected tails. Initial "
                        + "rejection stops freely with its separate none label. "
                        + "The overlap m=1,k=2 gives the same one-block cost."))),
                DescribeRole.Theorem))));
    }
}
