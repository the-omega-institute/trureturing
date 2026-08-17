using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PartialSummation;

internal sealed class AbelSummationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Abel summation rewrites a weighted range sum using prefix sums.",
        H("Finite Abel Summation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-abel-summation-for-a-range-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PartialSummation/AbelSummation.abel_summation_range"),
                H("Finite Abel summation for a range sum"),
                StatementSource.FromAuthor(AbelSummationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For scalar weights f and module-valued terms g, the weighted sum "
                            + "through n is the final weight times the full prefix sum, minus "
                            + "the sum of successive weight differences against shorter prefix "
                            + "sums.")),
                    Paragraph(Text(
                        "The source also continues to analytic localization and asymptotic "
                            + "claims. This declaration formalizes only its finite algebraic "
                            + "Abel-summation step.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Finset.sum_range_by_parts. The Lean proof "
                            + "imports and applies that theorem directly."))),
                DescribeRole.Theorem))));

    private static Formula AbelSummationFormula()
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula iSucc = Seq(i, Plus, D(1));
        Formula nPred = Seq(n, Minus, D(1));
        Formula fI = new Formula.Subscript(f, i);
        Formula fISucc = new Formula.Subscript(f, iSucc);
        Formula fNPred = new Formula.Subscript(f, nPred);
        Formula gI = new Formula.Subscript(g, i);
        Formula gJ = new Formula.Subscript(g, j);
        Formula weightedSum = Seq(
            Sum, Underscore, Grp(i, Lt, Sp, n), Sp, fI, Sp, Cdot, Sp, gI);
        Formula fullPrefix = Seq(Sum, Underscore, Grp(i, Lt, Sp, n), Sp, gI);
        Formula shortPrefix = Seq(Sum, Underscore, Grp(j, Lt, Sp, iSucc), Sp, gJ);
        Formula differenceSum = Seq(
            Sum, Underscore, Grp(i, Lt, Sp, nPred), Sp,
            Open, fISucc, Sp, Minus, Sp, fI, Close, Sp, Cdot, Sp, shortPrefix);

        return Disp(Seq(
            weightedSum, Sp, Eq, Sp,
            fNPred, Sp, Cdot, Sp, fullPrefix,
            Sp, Minus, Sp, differenceSum, Dot));
    }
}
