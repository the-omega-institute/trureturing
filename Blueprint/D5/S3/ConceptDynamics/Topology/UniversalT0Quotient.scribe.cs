using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class UniversalT0QuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The separation quotient has the universal property for continuous maps to T0 spaces.",
        H("Universal T0 Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("universal-t0-quotient"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Topology/UniversalT0Quotient."
                        + "universal_t0_quotient"),
                H("Universal property of the T0 quotient"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a topological space X, the canonical separation quotient is a T0 "
                            + "space and its projection q identifies precisely inseparable points.")),
                    Paragraph(Text(
                        "For every continuous map f from X to a T0 space Y, there is a unique "
                            + "continuous map from the separation quotient to Y whose composite "
                            + "with q is f. The proof uses Mathlib's separation-quotient lift, "
                            + "continuity theorem, and surjectivity of q.")),
                    Paragraph(Text(
                        "Pinned Mathlib searches found the exact declarations "
                            + "SeparationQuotient.lift, SeparationQuotient.continuous_lift, "
                            + "SeparationQuotient.lift_comp_mk, Inseparable.map, Inseparable.eq, "
                            + "and Function.Surjective.injective_comp_right; no repository "
                            + "theorem with this combined universal property was found."))),
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

    private static Formula Formula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula quotient = Seq(Operatorname, Grp(F.Id("SeparationQuotient")), Sp,
            source);
        Formula map = F.Id("f");
        Formula continuous = Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), map);
        Formula t0 = Typeclass("T0Space", target);
        Formula lifted = F.Id("barf");
        Formula projection = Seq(Operatorname, Grp(F.Id("mk")));
        Formula factorization = Seq(
            map, Sp, Eq, Sp, Compose(lifted, projection));
        Formula conclusion = Apply(
            Seq(Operatorname, Grp(F.Id("Continuous"))), lifted);
        Formula uniqueness = Seq(
            conclusion, Sp, Land, Sp, factorization);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, target, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("TopologicalSpace", source), Comma, Sp,
            Typeclass("TopologicalSpace", target), Comma, Sp,
            t0, Comma, Sp, map, Colon, Sp, Arrow(source, target), Comma, Sp,
            continuous, Sp, Rightarrow, Sp, Esc,
            Exists, Bang, Sp, lifted, Colon, Sp, Arrow(quotient, target), Comma, Sp,
            uniqueness, Dot));
    }
}
