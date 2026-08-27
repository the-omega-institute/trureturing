using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ObservationRankSubmodularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Linear/ObservationRankSubmodularity."
            + "observation_rank_submodularity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observation-subspace rank is submodular and has diminishing returns.",
        H("Observation Rank Submodularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-rank-submodularity"),
            DeclarationHandle.Create(Declaration),
            H("Observation rank is submodular"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let U assign a subspace of a finite-dimensional module to every "
                        + "observation index. For a finite selection A, its observation "
                        + "rank is the scalar dimension of the supremum of the selected "
                        + "subspaces.")),
                Paragraph(Text(
                    "The finite-supremum union identity identifies the combined selected "
                        + "space with a subspace supremum. The selected intersection embeds "
                        + "into the intersection of the two selected spaces, so the exact "
                        + "dimension formula for a supremum and infimum gives submodularity.")),
                Paragraph(Text(
                    "Applying the same inequality to A with the new index adjoined and to "
                        + "B yields the displayed diminishing-return form."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("V");
        Formula indexType = F.Id("iota");
        Formula subspaces = F.Id("U");
        Formula rank = F.Id("r");
        Formula selected = F.Id("A");
        Formula larger = F.Id("B");
        Formula added = F.Id("x");
        Formula type = TypeUniverse();
        Formula finiteSet = Call("Finset", indexType);
        Formula submodule = Call("Submodule", scalar, space);
        Formula subspaceFamily = Arrow(indexType, submodule);
        Formula union = Call("union", selected, larger);
        Formula intersection = Call("inter", selected, larger);
        Formula singleton = Call("singleton", added);
        Formula selectedWithAdded = Call("union", selected, singleton);
        Formula largerWithAdded = Call("union", larger, singleton);
        Formula rankDefinition = Seq(
            rank, Open, Typed(selected, finiteSet), Close, Sp, Colon, Eq, Sp,
            Call("finrank", scalar, Call("finsetSup", selected, subspaces)), Semi);
        Formula submodularity = Seq(
            Forall, Sp, Typed(Seq(selected, Comma, Sp, larger), finiteSet), Comma, Sp,
            Apply(rank, union), Sp, Plus, Sp, Apply(rank, intersection), Sp, Leq, Sp,
            Apply(rank, selected), Sp, Plus, Sp, Apply(rank, larger));
        Formula diminishingReturns = Seq(
            Forall, Sp, Typed(Seq(selected, Comma, Sp, larger), finiteSet), Comma, Sp,
            Typed(added, indexType), Comma, Sp,
            selected, Sp, Subseteq, Sp, larger, Sp, Rightarrow, Sp,
            Apply(rank, largerWithAdded), Sp, Minus, Sp, Apply(rank, larger), Sp,
            Leq, Sp,
            Apply(rank, selectedWithAdded), Sp, Minus, Sp, Apply(rank, selected));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, space, Comma, Sp, indexType), type),
                Comma),
            Seq(
                Grp(), OpenBracket, Call("DivisionRing", scalar), CloseBracket, Comma, Sp,
                OpenBracket, Call("AddCommGroup", space), CloseBracket, Comma, Sp,
                OpenBracket, Call("Module", scalar, space), CloseBracket, Comma),
            Seq(
                Grp(), OpenBracket, Call("FiniteDimensional", scalar, space), CloseBracket,
                Comma, Sp,
                OpenBracket, Call("DecidableEq", indexType), CloseBracket, Comma),
            Seq(
                Forall, Sp, Typed(subspaces, subspaceFamily), Comma, Sp,
                rankDefinition),
            Seq(Open, submodularity, Close, Sp, Land),
            Seq(Open, diminishingReturns, Close, Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

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
}
