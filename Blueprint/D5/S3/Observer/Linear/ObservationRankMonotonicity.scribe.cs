using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ObservationRankMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observation-subspace rank is monotone under inclusion.",
        H("Observation Rank Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-rank-monotonicity"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/ObservationRankMonotonicity."
                    + "observation_rank_monotonicity"),
            H("Adding observation settings cannot decrease rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Each setting contributes a subspace. Inclusion of selected index sets "
                    + "induces inclusion between their indexed subspace suprema, and "
                    + "finite-dimensional rank is monotone along that inclusion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("V");
        Formula indexType = F.Id("I");
        Formula subspaces = F.Id("U");
        Formula selected = F.Id("A");
        Formula larger = F.Id("B");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula submodule = Call("Submodule", scalar, space);
        Formula setOfIndices = Call("Set", indexType);
        Formula family = Seq(indexType, Sp, To, Sp, submodule);
        Formula selectedRank = Call(
            "finrank", scalar, Call("iSupOnSubtype", selected, subspaces));
        Formula largerRank = Call(
            "finrank", scalar, Call("iSupOnSubtype", larger, subspaces));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, space, Comma, Sp, indexType), type),
                Comma),
            Seq(
                Grp(), OpenBracket, Call("DivisionRing", scalar), CloseBracket,
                Comma, Sp,
                OpenBracket, Call("AddCommGroup", space), CloseBracket,
                Comma, Sp,
                OpenBracket, Call("Module", scalar, space), CloseBracket, Comma),
            Seq(
                Grp(), OpenBracket,
                Call("FiniteDimensional", scalar, space), CloseBracket, Comma),
            Seq(
                Forall, Sp, Typed(subspaces, family), Comma, Sp,
                Typed(Seq(selected, Comma, Sp, larger), setOfIndices), Comma),
            Seq(
                selected, Sp, Subseteq, Sp, larger, Sp, Rightarrow, Sp,
                selectedRank, Sp, Leq, Sp, largerRank, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

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
