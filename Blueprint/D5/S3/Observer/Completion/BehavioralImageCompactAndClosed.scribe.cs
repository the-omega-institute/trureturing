using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class BehavioralImageCompactAndClosedDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous behavior map from a compact state space into a Hausdorff dependent "
            + "product has compact and closed range.",
        H("Behavioral Image Compactness and Closedness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavioral-image-compact-and-closed"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/BehavioralImageCompactAndClosed."
                        + "behavioral_image_compact_and_closed"),
                H("The behavioral image is compact and closed"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed behavior map sends a state x to the dependent tuple of "
                            + "all coordinate readouts q_p(x). Coordinatewise continuity gives "
                            + "continuity into the product topology.")),
                    Paragraph(Text(
                        "The range of a continuous map from a compact space is compact. Every "
                            + "coordinate is Hausdorff, hence so is the dependent product, and a "
                            + "compact subset of that product is closed."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula pType = F.Id("P");
        Formula xType = F.Id("X");
        Formula lambda = F.Id("Lambda");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula readout = F.Id("q");
        Formula lambdaAt = Apply(lambda, p);
        Formula readoutAt = Apply(readout, p);
        Formula behaviorAt = Seq(
            x, Sp, Mapsto, Sp, Open, p, Sp, Mapsto, Sp,
            Apply(readoutAt, x), Close);
        Formula image = Call("range", behaviorAt);
        Formula coordinateTopologies = Seq(
            Forall, Sp, p, Colon, Sp, pType, Comma, Sp,
            Typeclass("TopologicalSpace", lambdaAt));
        Formula coordinateHausdorff = Seq(
            Forall, Sp, p, Colon, Sp, pType, Comma, Sp,
            Typeclass("T2Space", lambdaAt));
        Formula continuousCoordinates = Seq(
            Forall, Sp, p, Colon, Sp, pType, Comma, Sp,
            Call("Continuous", readoutAt));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, pType, Comma, Sp, xType, Colon, Sp, type, Comma, Sp,
            lambda, Colon, Sp, Arrow(pType, type), Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", xType), Comma, Sp,
            Typeclass("CompactSpace", xType), Comma, RowBreak, Grp(),
            coordinateTopologies, Comma, RowBreak, Grp(),
            coordinateHausdorff, Comma, RowBreak, Grp(),
            readout, Colon, Sp,
            Open, Forall, Sp, p, Colon, Sp, pType, Comma, Sp,
            Arrow(xType, lambdaAt), Close, Comma, RowBreak, Grp(),
            continuousCoordinates, Sp, Rightarrow, RowBreak, Grp(),
            Call("IsCompact", image), Sp, Land, RowBreak, Grp(),
            Call("IsClosed", image), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
