using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class PredictiveStateUniversalMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every sufficient past statistic uniquely determines the canonical predictive state on its realized image.",
        H("Predictive State Universal Minimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-state-universal-minimality"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality."
                    + "predictive_state_universal_minimality"),
            H("The predictive state is the coarsest sufficient past quotient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The future-law map supplies the canonical predictive state through its range "
                    + "factorization. If a statistic supports a predictor reproducing that law, "
                    + "there is exactly one map from the statistic's realized image to the "
                    + "future-law image that makes the canonical state factorization commute."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

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

    private static Formula TheoremFormula()
    {
        Formula past = F.Id("P");
        Formula interfaceType = F.Id("R");
        Formula futureType = F.Id("L");
        Formula future = F.Id("K");
        Formula statistic = F.Id("r");
        Formula predictor = F.Id("Kbar");
        Formula factor = F.Id("f");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula rangeR = Call("range", statistic);
        Formula rangeK = Call("range", future);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(past, Comma, Sp, interfaceType, Comma, Sp, futureType), type),
            Comma, RowBreak, Grp(),
            Typed(future, new Formula.TypeArrow(past, futureType)), Comma, Sp,
            Typed(statistic, new Formula.TypeArrow(past, interfaceType)), Comma, Sp,
            Typed(predictor, new Formula.TypeArrow(interfaceType, futureType)), Comma, RowBreak, Grp(),
            future, Sp, Eq, Sp, predictor, Sp, Circ, Sp, statistic, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp, Typed(factor, new Formula.TypeArrow(rangeR, rangeK)), Comma, Sp,
            Call("rangeFactorization", future), Sp, Eq, Sp,
            factor, Sp, Circ, Sp, Call("rangeFactorization", statistic), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
