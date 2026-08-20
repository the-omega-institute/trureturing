using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ControlledBehaviorUniversalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite controlled realization maps uniquely onto the complete behavior quotient.",
        H("Controlled Behavior Universality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-behavior-has-a-universal-minimal-realization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality."
                        + "controlled_behavior_universal_property"),
                H("Controlled behavior has a universal minimal realization"),
                StatementSource.FromAuthor(UniversalPropertyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite controlled state carrier with input-indexed updates "
                            + "and readout q. Let Z be the quotient by equality of every readout "
                            + "after every finite input word. Its projection, induced updates, "
                            + "and induced readout are defined directly from that behavior "
                            + "kernel.")),
                    Paragraph(Text(
                        "For any finite realization W reached surjectively from Y, commuting "
                            + "with every update and with the readout, there is a unique "
                            + "surjective factor h from W to Z. It factors the canonical "
                            + "projection, intertwines every realized update, and preserves the "
                            + "readout. Surjectivity gives card(Z) at most card(W).")),
                    Paragraph(Text(
                        "The factor is built from a right inverse of the realization map. "
                            + "Commutation along input words proves that different chosen "
                            + "preimages have equal complete behavior. Surjectivity of the "
                            + "canonical quotient projection proves surjectivity of h, while "
                            + "surjectivity onto W proves all equations and uniqueness pointwise.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied the exact declarations "
                            + "Setoid.quotientKerEquivRange and "
                            + "Fintype.card_le_of_surjective, both applied by the module. "
                            + "LeanSearch returned HTTP 404 for the shaped query, and local "
                            + "repository and pinned-library searches found no theorem "
                            + "packaging the complete universal property."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula UniversalPropertyFormula()
    {
        Formula yType = F.Id("Y");
        Formula inputType = F.Id("U");
        Formula outputType = F.Id("O");
        Formula realizedType = F.Id("W");
        Formula completionType = F.Id("Z");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula realization = F.Id("r");
        Formula realizedUpdate = F.Id("G");
        Formula realizedReadout = F.Id("o");
        Formula projection = Pi;
        Formula completedUpdate = Seq(Overline, Grp(F.Id("F")));
        Formula completedReadout = Seq(Overline, Grp(F.Id("q")));
        Formula factor = F.Id("h");
        Formula input = F.Id("u");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, yType, Comma, Sp, inputType, Comma, Sp, outputType,
            Comma, Sp, realizedType, Comma, RowBreak, Grp(),
            Typeclass("Fintype", yType), Comma, Sp,
            Typeclass("Fintype", realizedType), Comma, RowBreak,
            Typed("F", new Formula.TypeArrow(inputType,
                new Formula.TypeArrow(yType, yType))), Comma, Sp,
            Typed("q", new Formula.TypeArrow(yType, outputType)), Comma, RowBreak,
            Typed("r", new Formula.TypeArrow(yType, realizedType)), Comma, Sp,
            Typed("G", new Formula.TypeArrow(inputType,
                new Formula.TypeArrow(realizedType, realizedType))), Comma, Sp,
            Typed("o", new Formula.TypeArrow(realizedType, outputType)), Comma, RowBreak,
            Call("Surjective", realization), Sp, Rightarrow, Sp,
            Open, Forall, Sp, input, InMacro, Sp, inputType, Comma, Sp,
            realization, Sp, Circ, Sp, Apply(update, input), Sp, Eq, Sp,
            Apply(realizedUpdate, input), Sp, Circ, Sp, realization, Close,
            Sp, Rightarrow, Sp,
            readout, Sp, Eq, Sp, realizedReadout, Sp, Circ, Sp, realization,
            Sp, Rightarrow, RowBreak,
            Open, Exists, Bang, Sp, factor, Colon, Sp, realizedType, Sp, To, Sp,
            completionType, Comma, Sp, Call("Surjective", factor), Sp, Land, Sp,
            projection, Sp, Eq, Sp, factor, Sp, Circ, Sp, realization, Sp, Land,
            RowBreak, Open, Forall, Sp, input, InMacro, Sp, inputType, Comma, Sp,
            factor, Sp, Circ, Sp, Apply(realizedUpdate, input), Sp, Eq, Sp,
            Apply(completedUpdate, input), Sp, Circ, Sp, factor, Close, Sp, Land, RowBreak,
            completedReadout, Sp, Circ, Sp, factor, Sp, Eq, Sp, realizedReadout,
            Close, Sp, Land, Sp,
            Card(completionType), Sp, Leq, Sp, Card(realizedType), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
