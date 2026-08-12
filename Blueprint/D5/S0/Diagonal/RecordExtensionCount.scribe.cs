using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class RecordExtensionCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite candidate class restricted by fixed record values is bounded by its free choices.",
        H("Finite Record Extension Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("restricted-record-classes-have-at-most-the-free-choice-count"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/RecordExtensionCount.restricted_extension_card_le"),
                H("Restricted record classes have at most the free-choice count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("card")), Open,
                    F.Id("RestrictedExtensions"),
                    Open, F.Id("candidate"), Comma, Sp, F.Id("record"), Comma, Sp,
                    F.Id("prescribed"), Close, Close,
                    Sp, Le, Sp,
                    new Formula.Power(
                        Seq(Operatorname, Grp(F.Id("card")), Open, F.Id("Y"), Close),
                        Seq(
                        Operatorname, Grp(F.Id("card")), Open, F.Id("D"), Close,
                        Sp, Minus, Sp,
                        Operatorname, Grp(F.Id("card")), Open, F.Id("record"), Close))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let D and Y be finite types. A record is a finite set of positions in D, "
                        + "and prescribed supplies the fixed Y-value at each recorded position. "
                        + "RestrictedExtensions contains exactly the functions in an arbitrary "
                        + "candidate class that agree with those fixed values.")),
                    Paragraph(Text(
                        "All functions extending the record are equivalent to functions from the "
                        + "complement of the recorded positions into Y. Their exact cardinality is "
                        + "therefore card(Y) raised to card(D) minus card(record). Forgetting candidate "
                        + "membership embeds the restricted class into this full extension space and "
                        + "gives the displayed upper bound.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the finite upper-bound clause. It does "
                        + "not assert that a complexity-filtered candidate class eventually contains "
                        + "every extension, so the separate threshold and eventual-equality clause "
                        + "remains unresolved.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No direct theorem for functions "
                        + "agreeing with a fixed record was found. The proof wraps Fintype.card_fun, "
                        + "Fintype.card_subtype_compl, and Nat.card_le_card_of_injective after supplying "
                        + "the explicit record-extension equivalence."))),
                DescribeRole.Theorem)),
        []));
}
