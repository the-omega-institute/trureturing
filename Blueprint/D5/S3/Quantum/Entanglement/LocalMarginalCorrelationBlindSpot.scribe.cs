using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class LocalMarginalCorrelationBlindSpotDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula two = D(2);
        Formula mSquared = new Formula.Power(m, two);
        Formula nSquared = new Formula.Power(n, two);
        Formula localA = Call("localASector", m, n);
        Formula localB = Call("localBSector", m, n);
        Formula local = Call("Sup", localA, localB);
        Formula correlation = Call("correlationSector", m, n);
        Formula traceZero = Call("bipartiteTraceZero", m, n);
        Formula firstRank = Seq(mSquared, Sp, Minus, Sp, D(1));
        Formula secondRank = Seq(nSquared, Sp, Minus, Sp, D(1));
        Formula correlationRank = Seq(
            Grp(firstRank), Sp, Times, Sp, Grp(secondRank));
        Formula totalRank = Seq(
            Grp(mSquared), Sp, Grp(nSquared), Sp, Minus, Sp, D(1));
        Formula bell = Seq(Operatorname, Grp(F.Id("bellDensity")));
        Formula classical = F.Id("classicalCorrelatedDensity");
        Formula classicalSquared = new Formula.Power(classical, two);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, m, Comma, Sp, n, Comma, Sp,
            m, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            n, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            Grp(m), Sp, Times, Sp, Grp(n), Sp, Gt, Sp, D(1),
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Call("Sup", localA, localB, correlation), Sp, Eq, Sp, traceZero,
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", local), Sp, Eq, Sp,
            Grp(firstRank), Sp, Plus, Sp, Grp(secondRank),
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", correlation), Sp, Eq, Sp, correlationRank,
            Sp, Land, RowBreak, Grp(),
            Frac, Grp(Call("finrankR", correlation)), Grp(Call("finrankR", traceZero)),
            Sp, Eq, Sp, Frac, Grp(correlationRank), Grp(totalRank),
            Sp, Land, RowBreak, Grp(),
            Call("Orthogonal", local, correlation),
            Sp, Land, RowBreak, Grp(),
            Call("PosSemidef", bell), Sp, Land, Sp,
            Call("Tr", bell), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("rank", bell), Sp, Eq, Sp, D(1),
            Sp, Land, RowBreak, Grp(),
            Call("PosSemidef", classical), Sp, Land, Sp,
            Call("Tr", classical), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            classicalSquared, Sp, Neq, Sp, classical,
            Sp, Land, RowBreak, Grp(),
            Call("traceEnvironment", bell), Sp, Eq, Sp,
            Call("traceEnvironment", classical),
            Sp, Land, RowBreak, Grp(),
            Call("traceFirstFactor", bell), Sp, Eq, Sp,
            Call("traceFirstFactor", classical),
            Sp, Land, RowBreak, Grp(),
            bell, Sp, Neq, Sp, classical, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete local marginals leave every cross-factor correlation direction unread.",
            H("The Correlation Blind Spot of Local Marginals"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("local-marginal-correlation-blind-spot"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot."
                            + "local_marginal_correlation_blind_spot"),
                    H("Complete local data omit the full correlation sector"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For two positive finite factor dimensions with nontrivial product, "
                                + "the locally visible "
                                + "directions are the join of the two canonical local Hermitian "
                                + "sectors. Their real dimension is the sum of the two local "
                                + "traceless dimensions.")),
                        Paragraph(Text(
                            "The orthogonal unread sector is the canonical correlation sector. "
                                + "It has the product dimension, and its dimension "
                                + "divided by the full traceless dimension is the displayed "
                                + "correlation proportion.")),
                        Paragraph(Text(
                            "The final clauses give an explicit witness. The canonical Bell "
                                + "density is a positive trace-one rank-one state, while the "
                                + "diagonal equal mixture of the 00 and 11 basis states is a "
                                + "positive trace-one non-idempotent state.")),
                        Paragraph(Text(
                            "Both canonical partial traces agree for these two densities, but "
                                + "the global matrices differ. Thus even complete knowledge of "
                                + "both local marginals does not determine cross-factor "
                                + "correlations."))),
                    DescribeRole.Theorem))));
    }
}
