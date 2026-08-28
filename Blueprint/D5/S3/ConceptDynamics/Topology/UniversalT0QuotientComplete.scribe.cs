using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class UniversalT0QuotientCompleteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical separation quotient is T0 and has its unique continuous factorization.",
        H("Complete Universal T0 Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-universal-t0-quotient"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Topology/UniversalT0QuotientComplete."
                        + "universal_t0_quotient_complete"),
                H("The separation quotient is T0 and universal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source space and target space carry independent topologies, and the "
                            + "target is T0. The map f is an arbitrary continuous map between them.")),
                    Paragraph(Text(
                        "The first public conclusion records the canonical T0 structure on the "
                            + "separation quotient. The second gives the unique continuous factor "
                            + "whose composite with the canonical projection is f.")),
                    Paragraph(Text(
                        "The T0 structure is the pinned canonical Mathlib instance, while the "
                            + "factorization clause is supplied by the frozen family theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula quotient = Seq(Operatorname, Grp(F.Id("SeparationQuotient")), Sp, source);
        Formula map = F.Id("f");
        Formula continuous = Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), map);
        Formula lifted = F.Id("barf");
        Formula projection = Seq(Operatorname, Grp(F.Id("mk")));
        Formula factorization = Seq(map, Sp, Eq, Sp, Compose(lifted, projection));
        Formula liftedContinuous = Apply(
            Seq(Operatorname, Grp(F.Id("Continuous"))), lifted);
        Formula quotientT0 = Apply(
            Seq(Operatorname, Grp(F.Id("T0Space"))), quotient);
        Formula uniqueness = Seq(
            liftedContinuous, Sp, Land, Sp, factorization);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, target, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", source), Comma, Sp,
            Typeclass("TopologicalSpace", target), Comma, Sp,
            Typeclass("T0Space", target), Comma, RowBreak, Grp(),
            map, Colon, Sp, Arrow(source, target), Comma, Sp,
            continuous, Sp, Rightarrow, RowBreak, Grp(),
            quotientT0, Sp, Land, Sp,
            Esc, Exists, Bang, Sp, lifted, Colon, Sp, Arrow(quotient, target),
            Comma, Sp, uniqueness, Dot));
    }
}
