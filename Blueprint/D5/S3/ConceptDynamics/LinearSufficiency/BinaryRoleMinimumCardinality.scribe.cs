using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.LinearSufficiency;

internal sealed class BinaryRoleMinimumCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficient subfamily of binary roles has minimum size equal to the "
            + "dimension of their span.",
        H("Binary Role Minimum Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-role-minimum-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality."
                        + "binary_role_minimum_cardinality"),
                H("The minimum sufficient subfamily has the span dimension"),
                StatementSource.FromAuthor(MinimumCardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a family of candidate roles in a module over the "
                            + "binary field, and let H be the span of E.")),
                    Paragraph(Text(
                        "A selected subfamily B is sufficient exactly when it is drawn from E "
                            + "and spans the same submodule. A linearly independent spanning "
                            + "subfamily exists inside E and has cardinality equal to the "
                            + "dimension of H.")),
                    Paragraph(Text(
                        "Every other sufficient subfamily spans H, so the dimension bound for "
                            + "a generating family forces its cardinality to be at least "
                            + "that value. Thus the displayed value is attained and least."))),
                DescribeRole.Theorem))));

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

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula MinimumCardinalityFormula()
    {
        Formula carrier = F.Id("V");
        Formula candidates = F.Id("E");
        Formula chosen = F.Id("B");
        Formula cardinality = F.Id("kappa");
        Formula scalar = Call("ZMod", D(2));
        Formula family = Call("Set", carrier);
        Formula cardinals = F.Id("Cardinal");
        Formula Span(Formula family) => Call("span", scalar, family);
        Formula Card(Formula selected) => Call("card", selected);
        Formula admissibleCardinalities = Seq(
            OpenBrace,
            cardinality, Colon, Sp, cardinals, Sp, Mid, Sp,
            Exists, Sp, chosen, Colon, Sp, family, Comma, RowBreak, Grp(),
            chosen, Sp, Subseteq, Sp, candidates, Sp, Land, Sp,
            Span(chosen), Sp, Eq, Sp, Span(candidates), Sp, Land, Sp,
            Card(chosen), Sp, Eq, Sp, cardinality,
            CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Comma, Sp,
            Typeclass("AddCommGroup", carrier), Comma, Sp,
            Typeclass("Module", scalar, carrier), Comma, RowBreak, Grp(),
            candidates, Colon, Sp, family, Comma, RowBreak, Grp(),
            Call("IsLeast", admissibleCardinalities,
                Call("rank", scalar, Span(candidates))), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
