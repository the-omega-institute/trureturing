using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class FiniteSplitBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite equivalence partition can split strictly only within its initial class-count deficit.",
        H("Finite Split Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-refinement-count-le-card-sub-initial-classes"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/FiniteSplitBudget."
                        + "strict_refinement_count_le_card_sub_initial_classes"),
                H("Strict refinements consume the finite class-count budget"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite and let P_n be equivalence partitions of all of X. "
                            + "The Mathlib finpartition order is the refinement order, so "
                            + "P_(n+1) <= P_n says that each step may split classes but never "
                            + "merge them.")),
                    Paragraph(Text(
                        "A strict split is exactly an index where the next partition differs. "
                            + "The number of such indices is at most |X| minus the number of "
                            + "parts of P_0, which is the source's initial class count k_0.")),
                    Paragraph(Text(
                        "The proof directly applies the frozen finite-repair theorem. Pinned "
                            + "Mathlib supplies Finpartition.card_mono, "
                            + "Finpartition.card_parts_le_card, and Set.ncard_Ioc_nat to that "
                            + "underlying argument."))),
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
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula partitionAtIndex = Apply("P", index);
        Formula partitionAtSuccessor = Apply("P", Seq(index, Plus, D(1)));
        Formula changes = Seq(
            OpenBrace, index, InMacro, Sp, naturals, Sp, Mid, Sp,
            partitionAtSuccessor, Sp, Neq, Sp, partitionAtIndex, CloseBrace);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Fintype", carrier), Comma, Sp,
            Typeclass("DecidableEq", carrier), Comma, Esc,
            partition, Colon, Sp, naturals, Sp, To, Sp,
            Apply("Finpartition", carrier), Comma, Esc,
            Open, Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            partitionAtSuccessor, Sp, Subseteq, Sp, partitionAtIndex, Close, Sp,
            Rightarrow, RowBreak,
            Apply("ncard", changes), Sp, Leq, Sp,
            Cardinality(carrier), Sp, Minus, Sp,
            Apply("cardParts", Apply("P", D(0))), Dot));
    }
}
