using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FunctionalGraphs;

internal sealed class TraceRankJordanRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/FunctionalGraphs/TraceRankJordanRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete transfer traces and ranks recover the periodic and zero-block profiles.",
        H("Trace-Rank Jordan Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-difference-recovers-zero-blocks"),
                DeclarationHandle.Create(Prefix + "rank_difference_recovers_zero_blocks"),
                H("Rank differences recover zero blocks"),
                StatementSource.FromAuthor(RankDifferenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every positive index, successive residual ranks count zero blocks "
                        + "of at least that size, and the next difference counts exact size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-rank-spectra-determine-jordan-profile"),
                DeclarationHandle.Create(
                    Prefix + "trace_rank_spectra_determine_jordan_profile"),
                H("Trace and rank spectra determine the Jordan profile"),
                StatementSource.FromAuthor(ProfileUniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Möbius inversion uniquely recovers periodic cycle counts from traces. "
                        + "Stable-image ranks recover the periodic dimension, after which all "
                        + "residual ranks uniquely recover the nilpotent zero-block multiset."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Transfer(Formula update) => Call("transferOperator", update);

    private static Formula Power(Formula map, Formula exponent) => Call("pow", map, exponent);

    private static Formula Rank(Formula update, Formula exponent) =>
        Call("finrank", Call("Complex"), Call("range", Power(Transfer(update), exponent)));

    private static Formula ResidualRank(Formula update, Formula exponent) =>
        Call("natSub", Rank(update, exponent),
            Call("card", Call("PeriodicCore", update)));

    private static Formula Trace(Formula carrier, Formula update, Formula exponent) =>
        Call("trace", Call("Complex"), Call("Finsupp", carrier, Call("Complex")),
            Power(Transfer(update), exponent));

    private static Formula RankDifferenceFormula()
    {
        Formula type = F.Id("Type"), naturals = Call("Nat");
        Formula carrier = F.Id("Y"), update = F.Id("tau");
        Formula blocks = F.Id("zeroBlocks"), j = F.Id("j"), k = F.Id("k");
        Formula residual(Formula index) => ResidualRank(update, index);
        Formula increment(Formula index) =>
            Call("natSub", residual(Call("pred", index)), residual(index));
        Formula rankProfile = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", naturals)],
            Equal(
                residual(j),
                Call("natSub", Call("blockProfileDimension", blocks),
                    Call("blockKernelTower", blocks, j))));
        Formula conclusion = And(
            Equal(increment(k), Call("blockCountAtLeast", blocks, k)),
            Equal(Call("blockCountExactly", blocks, k),
                Call("natSub", increment(k), increment(Call("add", k, D(1))))));
        Formula assumptions = All(
            Call("Finite", carrier),
            rankProfile,
            Less(D(0), k));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Y", type),
                Bound("tau", Call("Function", carrier, carrier)),
                Bound("zeroBlocks", Call("BlockMultiset")),
                Bound("k", naturals),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula ProfileUniquenessFormula()
    {
        Formula type = F.Id("Type"), naturals = Call("Nat");
        Formula leftCarrier = F.Id("YLeft"), rightCarrier = F.Id("YRight");
        Formula tau = F.Id("tau"), sigma = F.Id("sigma");
        Formula leftCycles = F.Id("cycleCountsLeft");
        Formula rightCycles = F.Id("cycleCountsRight");
        Formula leftBlocks = F.Id("zeroBlocksLeft");
        Formula rightBlocks = F.Id("zeroBlocksRight");
        Formula r = F.Id("r"), k = F.Id("k");
        Formula divisorCycleSum(Formula index, Formula counts)
        {
            Formula divisor = F.Id("d");
            return Call("finsetSum", Call("divisors", index),
                Call("lambda", Call("typed", divisor, naturals),
                    Call("natCast", Call("Complex"),
                        Call("mul", divisor, Call("apply", counts, divisor)))));
        }
        Formula traceEquality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("r", naturals)],
            Implies(Less(D(0), r),
                Equal(Trace(leftCarrier, tau, r), Trace(rightCarrier, sigma, r))));
        Formula rankEquality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("k", naturals)],
            Equal(Rank(tau, k), Rank(sigma, k)));
        Formula cycleTrace(
            Formula carrier, Formula update, Formula counts) =>
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("r", naturals)],
                Implies(Less(D(0), r),
                    Equal(Trace(carrier, update, r),
                        divisorCycleSum(r, counts))));
        Formula zeroRanks(Formula update, Formula blocks) =>
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("k", naturals)],
                Equal(
                    ResidualRank(update, k),
                    Call("natSub", Call("blockProfileDimension", blocks),
                        Call("blockKernelTower", blocks, k))));
        Formula assumptions = All(
            Call("Finite", leftCarrier),
            Call("Finite", rightCarrier),
            traceEquality,
            rankEquality,
            Equal(Call("apply", leftCycles, D(0)), D(0)),
            Equal(Call("apply", rightCycles, D(0)), D(0)),
            cycleTrace(leftCarrier, tau, leftCycles),
            cycleTrace(rightCarrier, sigma, rightCycles),
            zeroRanks(tau, leftBlocks),
            zeroRanks(sigma, rightBlocks));
        Formula conclusion = And(
            Equal(leftCycles, rightCycles),
            Equal(leftBlocks, rightBlocks));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("YLeft", type),
                Bound("YRight", type),
                Bound("tau", Call("Function", leftCarrier, leftCarrier)),
                Bound("sigma", Call("Function", rightCarrier, rightCarrier)),
                Bound("cycleCountsLeft", Call("Function", naturals, naturals)),
                Bound("cycleCountsRight", Call("Function", naturals, naturals)),
                Bound("zeroBlocksLeft", Call("BlockMultiset")),
                Bound("zeroBlocksRight", Call("BlockMultiset")),
            ],
            Implies(assumptions, conclusion)));
    }
}
