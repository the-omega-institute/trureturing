using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Coding;

internal sealed class EventCodeIntertranslationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power and literal marker codes faithfully encode the same event quadruples.",
        H("Intertranslation of Event Godel Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("literal-marker-event-code-is-injective"),
                DeclarationHandle.Create(
                    "D5/S0/History/Coding/EventCodeIntertranslation.encode_event_injective"),
                H("The literal marker event code is injective"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")), Open,
                    Operatorname, Grp(F.Id("encodeEvent")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen marker implementation maps 0 to 00, maps 1 to 01, "
                        + "and places 11 between the source, opcode, argument, and tag "
                        + "fields. A public prefix decoder consumes exactly those pairs "
                        + "until 11, while fixed decoders recover the opcode and final tag.")),
                    Paragraph(Text(
                        "The decoder is proved to recover every encoded event, so equal "
                        + "marker histories force equality of all four event components. "
                        + "This supplies the injectivity asserted for the low-level implementation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-power-event-code-is-injective"),
                DeclarationHandle.Create(
                    "D5/S0/History/Coding/EventCodeIntertranslation.event_prime_code_injective"),
                H("The prime-power event code is injective"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")), Open,
                    Operatorname, Grp(F.Id("eventPrimeCode")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An event first becomes the four-entry natural sequence consisting "
                        + "of its source-history code, opcode index, argument-history code, "
                        + "and tag digit. The frozen primeSequenceCode then applies the "
                        + "successive-prime exponent formula with every exponent shifted by one.")),
                    Paragraph(Text(
                        "Injectivity is obtained by applying the frozen "
                        + "prime_sequence_code_injective theorem twice: once to recover the "
                        + "four components and once within each variable-length marker field. "
                        + "No second proof of the frozen prime-sequence theorem is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("event-code-intertranslation"),
                DeclarationHandle.Create(
                    "D5/S0/History/Coding/EventCodeIntertranslation.event_code_intertranslation"),
                H("Prime and marker implementations intertranslate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("e"), Comma, Sp,
                    Operatorname, Grp(F.Id("primeToMarkerCode")), Open,
                    Operatorname, Grp(F.Id("eventPrimeCode")), Open,
                    F.Id("e"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("encodeEvent")), Open,
                    F.Id("e"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("markerToPrimeCode")), Open,
                    Operatorname, Grp(F.Id("encodeEvent")), Open,
                    F.Id("e"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("eventPrimeCode")), Open,
                    F.Id("e"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two translations have different carriers: natural numbers for "
                        + "prime-power codes and marker histories for the literal implementation. "
                        + "Each translation recovers the common event on the image of its source "
                        + "encoder, then applies the other encoder.")),
                    Paragraph(Text(
                        "The displayed equations specify both directions on every encoded event. "
                        + "Behavior outside the two encoder images is deliberately unspecified; "
                        + "the inverse-on-range construction chooses a default there. This is not "
                        + "a reflexive equivalence disguised as an intertranslation.")),
                    Paragraph(Text(
                        "Pinned Mathlib searches found Function.leftInverse_invFun and "
                        + "List.map_injective_iff, which are applied for inverse-on-range and "
                        + "digit-list injectivity. No Mathlib or repository declaration matched "
                        + "the event-code bridge itself."))),
                DescribeRole.Theorem)),
        []));
}
