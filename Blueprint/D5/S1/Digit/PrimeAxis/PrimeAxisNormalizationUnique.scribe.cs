using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class PrimeAxisNormalizationUniqueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rowwise prime-axis sum has one canonical normalization, whose decoder is multiplication.",
        H("Unique Prime-Axis Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unique-prime-axis-normalization"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique.normalized_prime_axis_add_unique"),
                H("Rowwise prime-axis normalization is unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("z"), Comma, F.Id("w"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Exists, Bang, Sp, F.Id("result"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Open, Forall, Sp, F.Id("p"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxis")), Comma, Esc,
                    Operatorname, Grp(F.Id("CanonicalRaw")), Open,
                    F.Id("result"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("rawValue")), Open,
                    F.Id("result"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("rawValue")), Open,
                    F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("rawValue")), Open,
                    F.Id("w"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close,
                    Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("result"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close,
                    Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("w"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The result type enforces finite support, while the predicate states legality and exact "
                        + "axiswise preservation explicitly: every output row is canonical and represents the sum "
                        + "of the two input-row exponents. Existence is the established rowwise normalizer. "
                        + "Uniqueness follows independently on each prime axis from uniqueness of canonical W "
                        + "digits at a fixed raw value; extensionality then identifies the whole table.")),
                    Paragraph(Text(
                        "The same unique result satisfies the decoder equation already proved for rowwise "
                        + "normalization, so PZG table addition followed by normalization is ordinary "
                        + "multiplication after decoding."))),
                DescribeRole.Theorem
            )),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/Digit/PrimeAxisAddition"))]));
}
