using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FiniteFutureCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite future refinement stabilizes at the maximal invariant observation congruence.",
        H("Finite Future Congruence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-future-refinement-is-the-maximal-invariant-congruence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FiniteFutureCongruence."
                        + "finite_future_maximal_congruence"),
                H("Finite future refinement is the maximal invariant congruence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier Y, update tau, and observation q, let E_m "
                            + "relate states whose observations agree from time zero through "
                            + "time m. Let E_infinity require agreement at every finite time, "
                            + "and let Phi retain the current observation kernel while pulling "
                            + "a relation back through one update.")),
                    Paragraph(Text(
                        "The index m_star is the maximum, over all state pairs, of their first "
                            + "separation time, with zero assigned to pairs that never separate. "
                            + "The proof shows that E_infinity equals E_m_star and that m_star "
                            + "is no larger than any index where consecutive refinements agree. "
                            + "Thus this explicit index has the least-stabilization meaning used "
                            + "by the theorem.")),
                    Paragraph(Text(
                        "The stabilized relation is an equivalence relation inside the kernel "
                            + "of q, is preserved by tau, and contains every relation with those "
                            + "two containment and preservation properties. This stronger "
                            + "relation-level maximality immediately includes the stated "
                            + "maximality among equivalence relations.")),
                    Paragraph(Text(
                        "The repository fixed-point theorem supplies the exact greatest fixed "
                            + "point extremality result, backed by the pinned library OrderHom "
                            + "fixed-point declarations. Local and web searches found no theorem "
                            + "combining the recurrence, finite stabilization, maximality, and "
                            + "greatest-fixed-point clauses.")),
                    Paragraph(Text(
                        "The surrounding source assumes a nonempty carrier and a surjective "
                            + "observation map after replacing the output by its image. None of "
                            + "this theorem's clauses needs either restriction, so the checked "
                            + "statement proves the complete claim for every finite carrier and "
                            + "every observation map without adding a hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RelationAt(Formula index) =>
        new Formula.Subscript(F.Id("E"), index);

    private static Formula PairIn(Formula left, Formula right, Formula relation) =>
        Seq(Open, left, Comma, Sp, right, Close, Sp, InMacro, Sp, relation);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula observation = F.Id("q");
        Formula index = F.Id("m");
        Formula relation = F.Id("R");
        Formula left = F.Id("y");
        Formula right = F.Id("z");
        Formula zeroRelation = RelationAt(D(0));
        Formula finiteRelation = RelationAt(index);
        Formula successorRelation = RelationAt(Seq(index, Plus, D(1)));
        Formula infiniteRelation = RelationAt(Infty);
        Formula stableRelation = Call(
            "finiteFutureRelation",
            Tau,
            observation,
            Call("stabilizationIndex", Tau, observation));
        Formula kernel = Seq(Ker, Sp, observation);
        Formula refinement = Seq(Operatorname, Grp(F.Id("Phi")));
        Formula updateLeft = Apply(Tau, left);
        Formula updateRight = Apply(Tau, right);

        Formula finiteInfimum = Seq(
            Operatorname, Grp(F.Id("Inf")),
            Underscore, Grp(index, Sp, Geq, Sp, D(0)), Sp,
            finiteRelation);

        Formula recurrence = Seq(
            Forall, Sp, index, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            successorRelation, Sp, Eq, Sp, Apply(refinement, finiteRelation));

        Formula invariant = Seq(
            Forall, Sp, left, Comma, Sp, right, Comma, Sp,
            PairIn(left, right, infiniteRelation), Sp, Rightarrow, Sp,
            PairIn(updateLeft, updateRight, infiniteRelation));

        Formula maximal = Seq(
            Forall, Sp, relation, Comma, Sp,
            relation, Sp, Subseteq, Sp, kernel, Sp, Land, Sp,
            Open, Forall, Sp, left, Comma, Sp, right, Comma, Sp,
            PairIn(left, right, relation), Sp, Rightarrow, Sp,
            PairIn(updateLeft, updateRight, relation), Close,
            Sp, Rightarrow, Sp,
            relation, Sp, Subseteq, Sp, infiniteRelation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, state, Close, CloseBracket, Comma, Sp,
            Tau, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            observation, Colon, Sp, state, Sp, To, Sp, output, Comma, RowBreak,
            recurrence, Sp, Land, Sp,
            zeroRelation, Sp, Eq, Sp, kernel, Comma, RowBreak,
            infiniteRelation, Sp, Eq, Sp, finiteInfimum, Sp, Eq, Sp,
            stableRelation, Comma, RowBreak,
            Call("Equivalence", infiniteRelation), Sp, Land, Sp,
            infiniteRelation, Sp, Subseteq, Sp, kernel, Sp, Land, Sp,
            invariant, Comma, RowBreak,
            maximal, Comma, RowBreak,
            infiniteRelation, Sp, Eq, Sp,
            Nu, Sp, relation, Dot, Sp, Apply(refinement, relation), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
