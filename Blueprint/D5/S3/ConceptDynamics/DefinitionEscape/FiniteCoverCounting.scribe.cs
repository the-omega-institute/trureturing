using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class FiniteCoverCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula gamma = Gamma;
        Formula delta = Delta;
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula definition = F.Id("d");
        Formula budgetOne = Seq(F.Id("b"), Underscore, Grp(D(1)));
        Formula budgetTwo = Seq(F.Id("b"), Underscore, Grp(D(2)));
        Formula residual = Call("defectRelation", q, target);
        Formula blind = Call("blindResidual", gamma, q, target);
        Formula cut = Call(
            "intersection",
            residual,
            Call("complement", Call("conceptKernel", definition)));
        Formula cutsCover = Seq(
            Call("union", Seq(definition, Sp, InMacro, Sp, gamma), cut),
            Sp, Eq, Sp, residual);
        Formula finiteSufficient =
            Call("finiteSelectionSufficient", gamma, q, target);
        Formula marginal = Seq(
            Call("blindKernelReductionMeasure", gamma, q, target, definition),
            Underscore, Grp(F.Id("count")));
        Formula largerMarginal = Seq(
            Call("blindKernelReductionMeasure", delta, q, target, definition),
            Underscore, Grp(F.Id("count")));
        Formula rateOne = Seq(
            Call("budgetedEscapeRate", budgetOne), Underscore, Grp(F.Id("count")));
        Formula rateTwo = Seq(
            Call("budgetedEscapeRate", budgetTwo), Underscore, Grp(F.Id("count")));
        Formula statement = Disp(Seq(
            Open, blind, Sp, Eq, Sp, Emptyset, Close, Sp, Leftrightarrow, Sp,
            cutsCover, Comma, RowBreak, Grp(),
            Open, blind, Sp, Eq, Sp, Emptyset, Close, Sp, Rightarrow, Sp,
            finiteSufficient, Comma, RowBreak, Grp(),
            gamma, Sp, Subseteq, Sp, delta, Sp, Rightarrow, Sp,
            largerMarginal, Sp, Leq, Sp, marginal, Comma, RowBreak, Grp(),
            budgetOne, Sp, Leq, Sp, budgetTwo, Sp, Rightarrow, Sp,
            rateTwo, Sp, Leq, Sp, rateOne, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite definition cuts cover residuals with diminishing capture and antitone escape.",
            H("Finite Cover and Counting"),
            Blocks(Describe.Lean(
                DescribeId.Create("finite-cover-counting"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                        + "finite_cover_counting"),
                H("Finite residual covers control marginal capture and counting escape"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state type is finite and inhabited. The baseline residual is the "
                            + "canonical defectRelation. A definition cut is written directly as "
                            + "the part of that residual outside the imported conceptKernel; the "
                            + "module introduces no second residual or public cut-set definition.")),
                    Paragraph(Text(
                        "The first conjunct identifies sufficiency, represented by an empty "
                            + "blindResidual, with coverage by the union of all definition cuts. "
                            + "Mathlib finite_subset_iUnion then extracts a finite subfamily, and "
                            + "the accepted target recovery criterion turns its empty joined "
                            + "defect into finiteSelectionSufficient.")),
                    Paragraph(Text(
                        "For Gamma contained in Delta, every pair blind to Delta is blind to "
                            + "Gamma. Set.ncard_le_ncard therefore makes the imported blind-kernel "
                            + "reduction measure antitone in the accumulated definition family. "
                            + "A Boolean example makes the inequality strict: identity capture "
                            + "has positive marginal from the empty family and zero after identity "
                            + "has already been added.")),
                    Paragraph(Text(
                        "The counting escape-rate conjunct is not reproved. It instantiates the "
                            + "second conjunct of budgeted_escape_rate_bounds_and_antitone with "
                            + "finite ncard mass. Its explicit premises require a nonempty baseline "
                            + "defect and a feasible strategy at the smaller budget. A two-strategy "
                            + "Boolean probe computes rates one and zero, so reversing the budget "
                            + "direction produces a false inequality."))),
                DescribeRole.Theorem))));
    }
}
