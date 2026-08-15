using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ItineraryCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel classes, complete itineraries, and compatible finite words agree dynamically.",
        H("Itinerary Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-itinerary-completion-stabilizes"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/ItineraryCompletion."
                        + "itinerary_completion"),
                H("Finite itinerary completion stabilizes"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state type with deterministic update tau and "
                            + "readout q. Its complete itinerary records every future readout. "
                            + "The type Zq is the quotient of Y by equality of complete "
                            + "itineraries, while Iq is the range of the itinerary map. Each "
                            + "finite layer Xm is the range of the readout word through m.")),
                    Paragraph(Text(
                        "The compatible-family limit consists of one realized word at every "
                            + "depth, with later words restricting to earlier words. The theorem "
                            + "gives an equivalence from Zq to Iq and another from Iq to this "
                            + "limit. Both equivalences intertwine their update maps, which "
                            + "records the asserted dynamical naturality.")),
                    Paragraph(Text(
                        "For each distinguishable pair of states, choose one differing time. "
                            + "The supremum of these times over the finite state-pair type is a "
                            + "finite completion depth. Equality of words there forces equality "
                            + "of complete itineraries. It follows that coordinate projection "
                            + "from Iq to that finite layer is bijective, and every compatible "
                            + "family is represented by its stable coordinate.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supply the exact kernel-range equivalence "
                            + "Setoid.quotientKerEquivRange. Equiv.ofBijective packages the "
                            + "coordinate and compatible-family bijections, and Finset.le_sup "
                            + "bounds each chosen distinguishing time. LeanSearch returned HTTP "
                            + "404 for the shaped searches, and repository search found no equal "
                            + "or stronger finite-completion result."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula CompletionFormula()
    {
        Formula yType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula zq = F.Id("Zq");
        Formula iq = Call("Iq", yType);
        Formula limit = Call("CompatibleLimit", tau, q);
        Formula quotientUpdate = F.Id("Uq");
        Formula itineraryUpdate = F.Id("Ui");
        Formula limitUpdate = F.Id("Ul");
        Formula firstEquiv = F.Id("ez");
        Formula limitEquiv = F.Id("el");
        Formula depth = F.Id("m");
        Formula coordinateEquiv = F.Id("em");
        Formula finiteRange = Call("X", depth);
        Formula projection = Call("coordinateProjection", depth);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, yType, Comma, Sp, outputType, Comma, Sp,
            Typeclass("Fintype", yType), Comma, RowBreak,
            Typed("tau", new Formula.TypeArrow(yType, yType)), Comma, Sp,
            Typed("q", new Formula.TypeArrow(yType, outputType)), Comma, RowBreak,
            Exists, Sp, firstEquiv, Colon, Sp, zq, Sp, Equiv, Sp, iq, Comma, Sp,
            Call("Semiconj", firstEquiv, quotientUpdate, itineraryUpdate), Sp,
            Land, RowBreak,
            Exists, Sp, limitEquiv, Colon, Sp, iq, Sp, Equiv, Sp, limit, Comma, Sp,
            Call("Semiconj", limitEquiv, itineraryUpdate, limitUpdate), Sp,
            Land, RowBreak,
            Exists, Sp, depth, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Exists, Sp, coordinateEquiv, Colon, Sp, iq, Sp, Equiv, Sp, finiteRange,
            Comma, RowBreak,
            Call("toFun", coordinateEquiv), Sp, Eq, Sp, projection, Sp, Land, Sp,
            Call("Bijective", projection), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
