using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class FiniteRepairTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict refinements of a finite equivalence partition terminate within the available "
            + "class-count gap, while an infinite carrier admits an infinite refinement tower.",
        H("Finite Repair Termination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-repair-termination-and-infinite-tower"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/FiniteRepairTermination."
                        + "finite_repair_termination_and_infinite_tower"),
                H("Finite repair termination and the infinite boundary"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite and let P_n be a sequence of partitions of all of X. "
                            + "The order on Mathlib finpartitions is the refinement order, so "
                            + "P_(n+1) <= P_n says that every repair only splits equivalence "
                            + "classes and never merges them.")),
                    Paragraph(Text(
                        "The sequence is eventually constant. Moreover, the set of indices at "
                            + "which P_(n+1) differs from P_n has cardinality at most |X| minus "
                            + "the number of classes in P_0. This is the claimed sharp budget "
                            + "from the initial concept-class count to the discrete partition.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Finpartition.card_mono, "
                            + "Finpartition.card_parts_le_card, and "
                            + "WellFoundedLT.antitone_chain_condition. The local bookkeeping "
                            + "proves that a proper refinement has strictly more parts and "
                            + "injects strict change indices into the natural-number interval "
                            + "between the initial class count and |X|.")),
                    Paragraph(Text(
                        "Finiteness is essential: on the natural numbers, the kernel of "
                            + "x |-> min x n has singleton classes below n and one tail class. "
                            + "Increasing n strictly refines this relation forever, giving the "
                            + "source's infinite refinement tower. Inverse-limit construction "
                            + "and audit of a concrete realization are explicitly outside this "
                            + "mathematical declaration and remain implementation obligations."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula MainFormula()
    {
        Formula carrier = F.Id("X");
        Formula partition = F.Id("P");
        Formula index = F.Id("n");
        Formula stableIndex = F.Id("N");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula partitionAtIndex = Apply("P", index);
        Formula partitionAtSuccessor = Apply("P", Seq(index, Plus, D(1)));
        Formula partitionAtStable = Apply("P", stableIndex);
        Formula partitionAtZero = Apply("P", D(0));
        Formula changes = Seq(
            OpenBrace, index, InMacro, Sp, naturals, Sp, Mid, Sp,
            partitionAtSuccessor, Sp, Neq, Sp, partitionAtIndex, CloseBrace);
        Formula finiteClause = Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Fintype", carrier), Comma, Sp,
            Typeclass("DecidableEq", carrier), Comma, Esc,
            partition, Colon, Sp, naturals, Sp, To, Sp,
            Apply("Finpartition", carrier), Comma, Esc,
            Open, Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            partitionAtSuccessor, Sp, Subseteq, Sp, partitionAtIndex, Close, Sp,
            Rightarrow, RowBreak,
            Open,
            Exists, Sp, stableIndex, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            stableIndex, Sp, Leq, Sp, index, Sp, Rightarrow, Sp,
            partitionAtIndex, Sp, Eq, Sp, partitionAtStable,
            Close, Sp, Land, RowBreak,
            Apply("ncard", changes), Sp, Leq, Sp,
            Cardinality(carrier), Sp, Minus, Sp,
            Apply("cardParts", partitionAtZero));
        Formula tower = F.Id("E");
        Formula infiniteClause = Seq(
            Exists, Sp, tower, Colon, Sp, naturals, Sp, To, Sp,
            Apply("Setoid", naturals), Comma, Sp,
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            Apply("E", Seq(index, Plus, D(1))), Sp, Subset, Sp,
            Apply("E", index));

        return Disp(Seq(
            Open, finiteClause, Close, Sp, Land, RowBreak,
            Open, infiniteClause, Close, Dot));
    }
}
