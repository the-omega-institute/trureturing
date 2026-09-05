using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SkeletonSlotCnfDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete finite CNF admits every total first-return skeleton that fits the trace, published anchors, and allocated signature budget. Unused slots remain legal.",
        H("Finite Slot CNF for First-Return Skeletons"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slot-cnf-template-compilation"),
                DeclarationHandle.Create("D5/S0/Certificates/SkeletonSlotCNF.Requirement.toClause_sound"),
                H("Clause templates compile to native satisfiable clauses"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiler uses Std.Sat.CNF for literal polarity, clauses, and evaluation. Its templates are finite disjunction, exclusion, unit, implication, and two-premise implication. This module introduces no separate SAT checker."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slot-cnf-budget-allocation"),
                DeclarationHandle.Create("D5/S0/Certificates/SkeletonSlotCNF.slotsOfBudget"),
                H("Allocate the used return pairs inside a finite slot budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Enumerate the existing total skeleton's used output-return pairs, embed them in the available signature slots, and fill spare slots by repeating one existing pair. SlotWitness records equations to the existing Skeleton rather than a second evaluation semantics."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-cnf-model-to-sat"),
                DeclarationHandle.Create("D5/S0/Certificates/SkeletonSlotCNF.model_to_sat"),
                H("Local trace equations yield a satisfying assignment of generated CNF"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formula is generated from finite trace data and fixed capacities. It includes one-hot rows, both block actions, all four output labels, root states, the start-zero-loop, and the zero-output anchor.")),
                    Paragraph(Text("An intermediate signature color at each trace node factors the 10-edge clauses into a source-to-slot link and a slot-to-return implication. No reachability or symmetry-breaking condition is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slot-cnf-budget-model-satisfiability"),
                DeclarationHandle.Create("D5/S0/Certificates/SkeletonSlotCNF.budget_model_has_satisfying_assignment"),
                H("A total model within the signature budget satisfies the concrete formula"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The satisfying assignment and slot allocation are constructed. No caller-supplied model-to-SAT implication is an assumption. The finite-state enumeration uses classical choice only in the mathematical witness; formula generation itself is executable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slot-cnf-unsat-excludes-model"),
                DeclarationHandle.Create("D5/S0/Certificates/SkeletonSlotCNF.model_excluded_by_unsat"),
                H("Unsatisfiability excludes every model covered by the compiler"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A concrete native-CNF refutation would exclude the covered fixed-capacity models. The present module supplies no such refutation, no verified DIMACS byte translation, and no oracle-to-trace transport for the 79-power instance. Pinned Lean elaboration and axiom validation remain necessary before admission."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Automata/FiniteSampleSkeletonTotalization")),
        ]));
}
