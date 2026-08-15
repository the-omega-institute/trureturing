using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.NicaCovariance;

internal sealed class SemigroupRelationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The address shifts form semigroups whose coprime range projections satisfy Nica covariance.",
        H("Semigroup Relations and Nica Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("backward-shifts-compose-by-normalized-address-addition"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/SemigroupRelations."
                    + "backward_shift_comp"),
                H("Backward shifts form a semigroup"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableAdd")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Composing the backward shifts at u and v pulls a coefficient through two "
                    + "successive address translations. Associativity of multiplication under "
                    + "the prime-axis encoding identifies this with the single shift at their "
                    + "normalized table sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-translations-compose-by-normalized-address-addition"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/SemigroupRelations."
                    + "forward_translation_comp"),
                H("Forward translations form a semigroup"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableAdd")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two zero-extended forward translations have support exactly on the image "
                    + "of the composite address translation. On that image they recover the "
                    + "original coefficient in two stages, and away from it both sides vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-range-projections-satisfy-nica-covariance"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/SemigroupRelations."
                    + "shift_range_projection_comp_of_coprime"),
                H("Coprime range projections satisfy Nica covariance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")), Open,
                    Operatorname, Grp(F.Id("normalizedTableAdd")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each range projection is the divisibility filter for one encoded address. "
                    + "When the two encodings are coprime, passing both filters is equivalent to "
                    + "divisibility by their product, which is the encoding of the normalized "
                    + "table sum."))),
                DescribeRole.Theorem))));
}
