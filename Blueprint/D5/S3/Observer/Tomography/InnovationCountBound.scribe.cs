using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class InnovationCountBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-size innovations are bounded in count by the total information budget.",
        H("Large-Innovation Count Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-size-innovations-have-bounded-count"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/InnovationCountBound."
                        + "large_innovation_count_le_budget_div"),
                H("Fixed-size innovations have bounded count"),
                StatementSource.FromAuthor(InnovationCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h be a nonnegative summable real sequence of innovation sizes. "
                            + "Assume its infinite sum is at most the information budget H, and "
                            + "fix a positive threshold epsilon.")),
                    Paragraph(Text(
                        "Summability makes h tend to zero, so only finitely many indices can "
                            + "carry innovation at least epsilon. On that finite superlevel set, "
                            + "each term contributes at least epsilon. Its cardinality times "
                            + "epsilon is therefore bounded by the full series and hence by H.")),
                    Paragraph(Text(
                        "Two natural-language smart-search queries found no declaration-name "
                            + "match in pinned Mathlib. Local type-and-name search found and the "
                            + "proof applies Finset.card_nsmul_le_sum, Summable.sum_le_tsum, and "
                            + "Summable.tendsto_atTop_zero. Repository searches found no "
                            + "equivalent D5 declaration.")),
                    Paragraph(Text(
                        "This closes qdo-v1 corollary/38.3, atom "
                            + "qdo-residual-e5dbac2b7c4a0f3d76c61ebda4f98553c6d853ad567ef180d4d"
                            + "256371ca1771c. It formalizes the displayed count bound for an "
                            + "abstract innovation sequence. It does not define the source's "
                            + "specific entropy H(P) or identify a concrete observation tower's "
                            + "increments with h."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula InnovationCountFormula()
    {
        Formula innovation = F.Id("h");
        Formula budget = F.Id("H");
        Formula epsilon = F.Id("epsilon");
        Formula index = F.Id("k");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula largeLevels = Seq(
            OpenBrace, index, InMacro, Sp, natural, Sp, Mid, Sp,
            epsilon, Sp, Leq, Sp, Indexed(innovation, index), CloseBrace);
        Formula total = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp,
            Indexed(innovation, index));

        return Disp(Seq(
            Forall, Sp, innovation, Colon, Sp, natural, Sp, To, Sp, real, Comma, Esc,
            Forall, Sp, budget, Comma, Sp, epsilon, InMacro, Sp, real, Comma, Esc,
            Open, Forall, Sp, index, InMacro, Sp, natural, Comma, Sp,
            D(0), Sp, Leq, Sp, Indexed(innovation, index), Close, Sp, Land, Sp,
            Call("Summable", innovation), Sp, Land, Sp,
            total, Sp, Leq, Sp, budget, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, epsilon, Sp, Rightarrow, Sp,
            Call("ncard", largeLevels), Sp, Leq, Sp,
            Frac, Grp(budget), Grp(epsilon), Dot));
    }
}
