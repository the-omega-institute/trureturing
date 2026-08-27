using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class MultiContextBudgetLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Informationally complete normalized contexts obey a dimension lower bound.",
        H("Multi-Context Budget Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multi-context-budget-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound."
                        + "multi_context_budget_lower_bound"),
                H("Normalized contexts require enough independent outcomes"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The outcome directions live on the canonical real trace-zero "
                            + "Hermitian carrier. Each context has n_x plus one outcomes, "
                            + "and normalization makes their centered directions sum to zero.")),
                    Paragraph(Text(
                        "Injectivity is stated on positive trace-one density states. The "
                            + "canonical completeness equivalence turns it into full span. "
                            + "Dropping the last outcome of every context preserves that span, "
                            + "so its cardinality bounds the carrier dimension d squared minus one."))),
                DescribeRole.Theorem))));

    private static Formula BudgetFormula()
    {
        Formula d = F.Id("d"), context = F.Id("C"), count = F.Id("n");
        Formula effect = F.Id("E"), x = F.Id("x"), outcome = F.Id("j");
        Formula rho = Rho;
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula outcomeType = Call("Fin", Seq(Call("n", x), Plus, D(1)));
        Formula traceZero = Call("traceZeroHermitian", d);
        Formula effectAt = new Formula.Apply(effect, [x, outcome]);
        Formula effectType = Seq(
            Forall, Sp, x, Colon, Sp, context, Comma, Sp,
            outcomeType, Sp, To, Sp, traceZero);
        Formula normalized = Seq(
            Forall, Sp, x, Colon, Sp, context, Comma, Sp,
            Sum, Underscore, Grp(Seq(outcome, InMacro, Sp, outcomeType)), Sp,
            effectAt, Sp, Eq, Sp, D(0));
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula signature = Seq(
            Open, rho, Colon, Sp, stateType, Sp, Mapsto, Sp,
            Open, x, Colon, Sp, context, Sp, Mapsto, Sp,
            Open, outcome, Colon, Sp, outcomeType, Sp, Mapsto, Sp,
            Re, Sp, Call("Tr", Seq(Call("matrix", rho), Sp, effectAt)), Close,
            Close, Close);
        Formula independentBudget = Seq(
            Sum, Underscore, Grp(Seq(x, InMacro, Sp, context)), Sp,
            Call("n", x));

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak, Grp(),
            context, Colon, Sp, type, Comma, Sp, Call("Fintype", context), Comma,
            RowBreak, Grp(),
            count, Colon, Sp, context, Sp, To, Sp, naturals, Comma, RowBreak, Grp(),
            effect, Colon, Sp, effectType, Comma, RowBreak, Grp(),
            normalized, Comma, RowBreak, Grp(),
            Call("Injective", signature), Sp, Rightarrow, RowBreak, Grp(),
            new Formula.Power(d, D(2)), Minus, D(1), Sp, Leq, Sp,
            independentBudget, Dot));
    }
}
