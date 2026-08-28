using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class TransitiveInvariantDistributionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula group = F.Id("G");
        Formula actionCarrier = F.Id("A");
        Formula law = F.Id("mu");
        Formula groupElement = F.Id("g");
        Formula point = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula pmfType = Call("PMF", actionCarrier);
        Formula invariant = Seq(
            Forall, Sp, groupElement, Colon, Sp, group, Comma, Sp,
            point, Colon, Sp, actionCarrier, Comma, Sp,
            Apply(law, Seq(groupElement, Sp, F.Id("smul"), Sp, point)),
            Sp, Eq, Sp, Apply(law, point));
        Formula pointMass = Seq(
            Forall, Sp, point, Colon, Sp, actionCarrier, Comma, Sp,
            Apply(law, point), Sp, Eq, Sp,
            Seq(Call("card", actionCarrier), Caret, Grp(Seq(Minus, D(1)))));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(group, type), Comma, Sp, Typed(actionCarrier, type),
            Comma, RowBreak, Grp(),
            Call("Group", group), Sp, Land, Sp,
            Call("Fintype", actionCarrier), Sp, Land, Sp,
            Call("Nonempty", actionCarrier), Sp, Land, RowBreak, Grp(),
            Call("MulAction", group, actionCarrier), Sp, Land, Sp,
            Call("IsPretransitive", group, actionCarrier), Sp, Rightarrow, RowBreak, Grp(),
            Grp(Seq(
                Exists, Sp, Bang, Sp, law, Colon, Sp, pmfType, Comma, Sp, invariant)),
            Sp, Land, RowBreak, Grp(),
            Grp(Seq(
                Forall, Sp, law, Colon, Sp, pmfType, Comma, Sp,
                invariant, Sp, Rightarrow, Sp, pointMass)), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A transitive action admits exactly the uniform invariant probability mass function.",
            H("Transitive Invariant Distribution"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("transitive-invariant-distribution-is-uniquely-uniform"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/"
                            + "TransitiveInvariantDistribution."
                            + "transitive_invariant_distribution_unique_uniform"),
                    H("The invariant law is uniquely uniform"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Transitivity sends any chosen point to any other point. Invariance "
                                + "therefore forces all point masses of a candidate law to agree.")),
                        Paragraph(Text(
                            "The total mass is one, so cancellation by the nonzero finite carrier "
                                + "cardinality identifies that common value with the uniform mass.")),
                        Paragraph(Text(
                            "The argument proves both the unique invariant probability mass "
                                + "function and its public pointwise cardinality formula."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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
