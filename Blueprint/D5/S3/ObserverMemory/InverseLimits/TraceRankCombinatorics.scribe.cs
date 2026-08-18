using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class TraceRankCombinatoricsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer-operator traces and range ranks count finite-map combinatorics.",
        H("Trace and Rank Combinatorics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-rank-combinatorial-meaning"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics."
                        + "trace_rank_combinatorial_meaning"),
                H("Trace counts fixed points and rank counts the iterated image"),
                StatementSource.FromAuthor(TraceRankFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a self-map act on the standard basis of the finite complex vector "
                            + "space by sending the basis vector at a state to the basis vector "
                            + "at its image.")),
                    Paragraph(Text(
                        "The diagonal entry of a positive operator power is one exactly at a "
                            + "fixed point of the corresponding iterate, so the trace is the "
                            + "number of those fixed points.")),
                    Paragraph(Text(
                        "The range of an arbitrary natural power is spanned by the distinct "
                            + "basis vectors indexed by the iterated image. Their linear "
                            + "independence makes the range dimension equal its cardinality.")),
                    Paragraph(Text(
                        "Repository search found no equal or stronger combined theorem. Pinned "
                            + "Mathlib supplies trace_eq_matrix_trace, range_lmapDomain, "
                            + "lmapDomain_comp, basisSingleOne, and finrank_span_set_eq_card; "
                            + "the proof applies those declarations directly."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TraceRankFormula()
    {
        Formula carrier = F.Id("Y");
        Formula map = Tau;
        Formula positivePower = F.Id("r");
        Formula power = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula transferR = Seq(
            Apply(F.Id("transferOperator"), map), Caret, Grp(positivePower));
        Formula transferK = Seq(
            Apply(F.Id("transferOperator"), map), Caret, Grp(power));
        Formula iterateR = Seq(map, Caret, Grp(positivePower));
        Formula iterateK = Seq(map, Caret, Grp(power));

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp,
            Operatorname, Grp(F.Id("Finite")), Open, carrier, Close, Comma, Sp,
            Forall, Sp, map, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            Forall, Sp, positivePower, Comma, Sp, power, Sp, InMacro, Sp, naturals,
            Comma, Esc, D(1), Sp, Leq, Sp, positivePower, Sp, Rightarrow, Sp, Nl,
            Open,
            Operatorname, Grp(F.Id("Tr")), Open, transferR, Close, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("card")), Open,
            Operatorname, Grp(F.Id("Fix")), Open, iterateR, Close, Close,
            Sp, Land, Sp, Nl,
            Operatorname, Grp(F.Id("finrank")), Open,
            Operatorname, Grp(F.Id("range")), Open, transferK, Close, Close,
            Sp, Eq, Sp,
            Operatorname, Grp(F.Id("card")), Open,
            Operatorname, Grp(F.Id("image")), Open, iterateK, Close, Close,
            Close, Dot));
    }
}
