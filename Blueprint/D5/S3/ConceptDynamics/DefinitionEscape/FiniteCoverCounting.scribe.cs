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
        Formula family = Seq(F.Id("d"), Underscore, Grp(F.Id("i")));
        Formula budgetOne = Seq(F.Id("b"), Underscore, Grp(D(1)));
        Formula budgetTwo = Seq(F.Id("b"), Underscore, Grp(D(2)));
        Formula residual = Call("defectRelation", q, target);
        Formula gammaBlind = Call(
            "intersection",
            residual,
            Call("jointKernel", gamma, family));
        Formula deltaBlind = Call(
            "intersection",
            residual,
            Call("jointKernel", delta, family));
        Formula cut = Call(
            "intersection",
            residual,
            Call("complement", Call("conceptKernel", definition)));
        Formula cutsCover = Seq(
            Call("union", Seq(definition, Sp, InMacro, Sp, gamma), cut),
            Sp, Eq, Sp, residual);
        Formula finiteSufficient = Call(
            "finiteSelectionSufficientOnRange", gamma, family, q, target);
        Formula marginal = Call(
            "nu",
            Call("intersection", gammaBlind,
                Call("complement", Call("conceptKernel", definition))));
        Formula largerMarginal = Call(
            "nu",
            Call("intersection", deltaBlind,
                Call("complement", Call("conceptKernel", definition))));
        Formula marginalPremises = new Formula.Logic(
            Seq(gamma, Sp, Subseteq, Sp, delta),
            FormulaLogicOperator.And,
            Seq(Neg, Open, definition, Sp, InMacro, Sp, delta, Close));
        Formula rateOne = Seq(
            Call("budgetedEscapeRate", budgetOne), Underscore, Grp(F.Id("count")));
        Formula rateTwo = Seq(
            Call("budgetedEscapeRate", budgetTwo), Underscore, Grp(F.Id("count")));
        Formula baselineNonempty = Call("Nonempty", residual);
        Formula strategy = F.Id("s");
        Formula feasibleAtBudgetOne = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [new Formula.BoundVariable(
                FormulaIdentifier.Create("s"),
                F.Id("Strategy"))],
            new Formula.Relation(
                Call("cost", strategy),
                FormulaRelationOperator.LessThanOrEqual,
                budgetOne));
        Formula groupedFeasibleAtBudgetOne = Seq(
            Open, feasibleAtBudgetOne, Close);
        Formula budgetOrdered = new Formula.Relation(
            budgetOne,
            FormulaRelationOperator.LessThanOrEqual,
            budgetTwo);
        Formula countingAntitone = new Formula.Relation(
            rateTwo,
            FormulaRelationOperator.LessThanOrEqual,
            rateOne);
        Formula countingPremises = new Formula.Logic(
            new Formula.Logic(
                baselineNonempty,
                FormulaLogicOperator.And,
                groupedFeasibleAtBudgetOne),
            FormulaLogicOperator.And,
            budgetOrdered);
        Formula countingClause = new Formula.Logic(
            countingPremises,
            FormulaLogicOperator.Implies,
            countingAntitone);
        Formula statement = Disp(Seq(
            Open, gammaBlind, Sp, Eq, Sp, Emptyset, Close, Sp, Leftrightarrow, Sp,
            cutsCover, Comma, RowBreak, Grp(),
            Open, gammaBlind, Sp, Eq, Sp, Emptyset, Close, Sp, Rightarrow, Sp,
            finiteSufficient, Comma, RowBreak, Grp(),
            Open, marginalPremises, Close, Sp, Rightarrow, Sp,
            largerMarginal, Sp, Leq, Sp, marginal, Comma, RowBreak, Grp(),
            countingClause, Dot));

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
                        "The state type is finite; it need not be inhabited. Candidate definitions "
                            + "are indexed by I with a dependent codomain family V : I -> Type and "
                            + "readouts d_i : X -> V(i). Gamma and Delta are index sets, and the "
                            + "imported dependent jointKernel is used directly. The supplement in "
                            + "the counting clause has its own unrelated codomain.")),
                    Paragraph(Text(
                        "The first conjunct identifies an empty target defect intersected with the "
                            + "dependent family joint kernel with coverage by all definition cuts. "
                            + "Mathlib finite_subset_iUnion extracts a finite subfamily. The second "
                            + "conjunct constructs recovery only on Set.range of that finite joint "
                            + "readout, so it also holds for an empty state and empty target; the "
                            + "stronger whole-codomain recovery requirement is false there.")),
                    Paragraph(Text(
                        "For Gamma contained in Delta and a fresh candidate d, every pair blind to "
                            + "Delta is blind to Gamma. Monotonicity of the parameter nu therefore "
                            + "makes weighted marginal capture antitone in the accumulated family. "
                            + "A Boolean witness uses a non-counting point weight of three: negation "
                            + "removes the weighted pair before identity arrives, so capture falls "
                            + "strictly and the reversed inequality is false.")),
                    Paragraph(Text(
                        "Only the fourth conjunct is specialized to counting. It instantiates the "
                            + "second conjunct of budgeted_escape_rate_bounds_and_antitone with "
                            + "finite ncard mass. Its explicit premises require a nonempty baseline "
                            + "defect and a feasible strategy at the smaller budget. A two-strategy "
                            + "Boolean probe computes rates one and zero, so reversing the budget "
                            + "direction produces a false inequality."))),
                DescribeRole.Theorem))));
    }
}
