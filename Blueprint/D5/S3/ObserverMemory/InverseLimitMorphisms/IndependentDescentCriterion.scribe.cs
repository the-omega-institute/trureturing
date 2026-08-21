using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimitMorphisms;

internal sealed class IndependentDescentCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-limit descent and its coordinate-liftable converse have independent premises.",
        H("Independent Inverse-Limit Descent Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inverse-limit-descent-and-independent-converse"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion."
                        + "inverse_limit_descent_and_independent_converse"),
                H("Unique descent and the independent coordinate-liftable converse"),
                StatementSource.FromAuthor(DescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S and T be inverse-stage systems over a preordered index type, and "
                            + "let delta be a family of maps between corresponding stages. The "
                            + "first public conjunct assumes finite naturality and concludes the "
                            + "existence and uniqueness of the coordinate-compatible map between "
                            + "compatible-family limits.")),
                    Paragraph(Text(
                        "The second public conjunct is independent: it assumes every source "
                            + "coordinate projection is surjective and that some map between the "
                            + "compatible-family limits has the coordinate equation. Those two "
                            + "premises recover finite naturality; finite naturality is not an "
                            + "ambient hypothesis of this converse.")),
                    Paragraph(Text(
                        "The proof imports the canonical inverse-stage and compatible-family "
                            + "types. It applies the frozen predecessor only to the valid forward "
                            + "half, while the converse lifts an arbitrary finite-stage value and "
                            + "uses compatibility of the two limit families."))),
                DescribeRole.Theorem))));

    private static Formula Stage(Formula family, Formula index) =>
        Seq(family, Underscore, Grp(index));

    private static Formula Projection(Formula system, Formula index) =>
        Seq(Pi, Underscore, Grp(index), Caret, Grp(system));

    private static Formula Restriction(Formula name, Formula high, Formula low) =>
        Seq(name, Underscore, Grp(high, Comma, low));

    private static Formula CoordinateEquation(
        Formula limitMap,
        Formula source,
        Formula target,
        Formula delta,
        Formula index) =>
        Seq(Projection(target, index), Sp, Circ, Sp, limitMap, Sp, Eq, Sp,
            Stage(delta, index), Sp, Circ, Sp, Projection(source, index));

    private static Formula Naturality(
        Formula sourceRestriction,
        Formula targetRestriction,
        Formula delta,
        Formula high,
        Formula low) =>
        Seq(Restriction(targetRestriction, high, low), Sp, Circ, Sp,
            Stage(delta, high), Sp, Eq, Sp, Stage(delta, low), Sp, Circ, Sp,
            Restriction(sourceRestriction, high, low));

    private static Formula DescentFormula()
    {
        Formula indexType = F.Id("I");
        Formula source = F.Id("S");
        Formula target = F.Id("T");
        Formula delta = F.Id("delta");
        Formula high = F.Id("j");
        Formula low = F.Id("i");
        Formula sourceRestriction = F.Id("P");
        Formula targetRestriction = F.Id("Q");
        Formula limitMap = F.Id("Delta");
        Formula forwardNaturality = Naturality(
            sourceRestriction, targetRestriction, delta, high, low);
        Formula coordinateEquation = CoordinateEquation(
            limitMap, source, target, delta, low);
        Formula uniqueDescent = Seq(
            Exists, Bang, Sp, limitMap, Comma, Sp,
            Forall, Sp, low, Comma, Sp, coordinateEquation);
        Formula forward = Seq(
            Open, Forall, Sp, high, Comma, Sp, low, Comma, Sp,
            high, Sp, Geq, Sp, low, Comma, Sp, forwardNaturality, Close,
            Sp, Rightarrow, Sp, uniqueDescent);
        Formula liftable = Seq(
            Forall, Sp, low, Comma, Sp,
            CallSurjective(Projection(source, low)));
        Formula mapExists = Seq(
            Exists, Sp, limitMap, Comma, Sp,
            Forall, Sp, low, Comma, Sp, coordinateEquation);
        Formula reverse = Seq(
            Open, Open, liftable, Close, Sp, Land, Sp, mapExists, Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, high, Comma, Sp, low, Comma, Sp,
            high, Sp, Geq, Sp, low, Comma, Sp, forwardNaturality);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, indexType, Comma, Sp,
            source, Comma, Sp, target, Comma, Sp, delta, Comma, RowBreak, Grp(),
            Open, forward, Close, Sp, Land, RowBreak, Grp(),
            Open, reverse, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CallSurjective(Formula projection) =>
        Seq(Operatorname, Grp(F.Id("Surjective")), Open, projection, Close);
}
