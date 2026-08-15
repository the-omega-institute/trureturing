using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class PrimeLedgerGroupificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural prime ledgers are forward-only; signed ledgers record explicit inverses.",
        H("Prime Ledger Direction and Groupification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("natural-ledgers-are-forward-only-and-signed-ledgers-record-inverses"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Embeddings/PrimeLedgerGroupification.prime_ledger_direction_and_groupification"),
                H("Natural ledgers are forward-only and signed ledgers record inverses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("z"), Comma, Esc,
                    Open, Open, Exists, Sp, F.Id("f"), Colon, Sp,
                    F.Id("NaturalPrimeLedger"), Comma, Sp,
                    F.Id("naturalLedgerCast"), Open, F.Id("f"), Close, Eq, F.Id("z"), Close,
                    Sp, Iff, Sp, Open, Forall, Sp, F.Id("p"), Comma, Sp,
                    D(0), Leq, Sp, F.Id("z"), Underscore, F.Id("p"), Close, Close,
                    Sp, Land, RowBreak,
                    Exists, Sp, F.Id("f"), Comma, F.Id("i"), Colon, Sp,
                    F.Id("NaturalPrimeLedger"), Comma, Esc,
                    F.Id("z"), Eq, F.Id("naturalLedgerCast"), Open, F.Id("f"), Close,
                    Minus, F.Id("naturalLedgerCast"), Open, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite signed prime ledger comes from a natural prime ledger exactly "
                        + "when every exponent is nonnegative. Thus a ledger with no inverse "
                        + "component can move only in the coordinatewise forward direction.")),
                    Paragraph(Text(
                        "Every signed ledger also has an explicit forward-minus-inverse presentation. "
                        + "The forward ledger records the positive part of each exponent and the "
                        + "inverse ledger records the positive part of its negation, so negative "
                        + "exponents occur only through the second recorded ledger.")),
                    Paragraph(Text(
                        "The library was searched before proving. Finsupp.mapRange constructs both "
                        + "finite natural ledgers, Int.toNat_of_nonneg identifies the nonnegative "
                        + "image, and the exact Mathlib identity Int.toNat_sub_toNat_neg supplies the "
                        + "pointwise groupification decomposition. The theorem applies these pinned "
                        + "components directly."))),
                DescribeRole.Theorem))));
}
