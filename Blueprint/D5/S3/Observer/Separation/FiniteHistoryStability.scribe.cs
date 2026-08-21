using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FiniteHistoryStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observation histories stabilize and their class growth is bounded by the finite carrier.",
        H("Finite History Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-history-stability"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FiniteHistoryStability.finite_history_stability"),
                H("Finite history stability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier X, update tau, and readout q, let R_m "
                            + "relate states whose observations agree from time zero through "
                            + "time m, and let R_infinity require agreement at every finite "
                            + "future time. The quotient class count at depth m is c_m.")),
                    Paragraph(Text(
                        "The finite relations decrease with depth, while their quotient class "
                            + "counts increase. A finite stability depth m_star reaches the "
                            + "infinite-future relation, and every later depth has that same "
                            + "relation.")),
                    Paragraph(Text(
                        "Each strict refinement before m_star consumes a new quotient class. "
                            + "Consequently m_star is bounded by c_m_star minus c_0, and that "
                            + "increase is at most the carrier cardinality minus c_0. The proof "
                            + "handles the empty finite carrier directly and uses a private "
                            + "range corestriction only to apply the existing surjective-readout "
                            + "bound.")),
                    Paragraph(Text(
                        "The source's qualitative remark that the depth may depend on the whole "
                            + "system has no in-scope quantitative predicate and is therefore "
                            + "not asserted as a universal formal clause."))),
                DescribeRole.Theorem))));

    private static Formula RelationAt(Formula index) =>
        new Formula.Subscript(F.Id("R"), index);

    private static Formula CountAt(Formula index) =>
        new Formula.Subscript(F.Id("c"), index);

    private static Formula PairIn(Formula left, Formula right, Formula relation) =>
        Seq(Open, left, Comma, Sp, right, Close, Sp, InMacro, Sp, relation);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("Q");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula index = F.Id("m");
        Formula depth = new Formula.Subscript(F.Id("m"), Star);
        Formula relation = RelationAt(index);
        Formula successorRelation = RelationAt(Seq(index, Plus, D(1)));
        Formula stableRelation = RelationAt(depth);
        Formula infiniteRelation = RelationAt(Infty);
        Formula count = CountAt(index);
        Formula stableCount = CountAt(depth);
        Formula initialCount = CountAt(D(0));
        Formula classDifference = Seq(stableCount, Sp, Minus, Sp, initialCount);
        Formula carrierDifference = Seq(
            Cardinality(state), Sp, Minus, Sp, initialCount);
        Formula depthDefinition = Seq(
            depth, Sp, Eq, Sp, Operatorname, Grp(F.Id("sInf")), Sp,
            OpenBrace, index, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
            Mid, Sp, relation, Sp, Eq, Sp, successorRelation, CloseBrace);
        Formula countDefinition = Seq(
            count, Sp, Eq, Sp, Cardinality(Seq(state, Sp, Slash, Sp, relation)));
        Formula finiteRelation = Seq(
            Forall, Sp, index, Comma, Sp,
            PairIn(F.Id("x"), F.Id("y"), successorRelation), Sp,
            Rightarrow, Sp, PairIn(F.Id("x"), F.Id("y"), relation));
        Formula countGrowth = Seq(
            Forall, Sp, index, Comma, Sp,
            count, Sp, Leq, Sp, CountAt(Seq(index, Plus, D(1))));
        Formula stableFuture = Seq(
            stableRelation, Sp, Eq, Sp, infiniteRelation);
        Formula permanence = Seq(
            Forall, Sp, F.Id("n"), Comma, Sp,
            depth, Sp, Leq, Sp, F.Id("n"), Sp, Rightarrow, Sp,
            RelationAt(F.Id("n")), Sp, Eq, Sp, infiniteRelation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, state, Close, CloseBracket, Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, RowBreak, Grp(),
            countDefinition, Comma, Sp, depthDefinition, Comma, RowBreak, Grp(),
            finiteRelation, Sp, Land, Sp, RowBreak, Grp(),
            countGrowth, Sp, Land, Sp, RowBreak, Grp(),
            stableFuture, Sp, Land, Sp, RowBreak, Grp(),
            permanence, Sp, Land, Sp, RowBreak, Grp(),
            depth, Sp, Leq, Sp, classDifference, Sp, Land, Sp, RowBreak, Grp(),
            classDifference, Sp, Leq, Sp, carrierDifference, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Cardinality(Formula type) =>
        Seq(Lvert, Sp, type, Sp, Rvert);
}
