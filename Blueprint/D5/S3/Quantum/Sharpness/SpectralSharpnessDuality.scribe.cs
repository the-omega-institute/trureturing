using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class SpectralSharpnessDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral sharpness is the attained maximum of bounded spectral pairings.",
        H("Spectral Sharpness as a Bounded-Pairing Maximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-sharpness-is-greatest-bounded-pairing"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/SpectralSharpnessDuality."
                    + "spectral_sharpness_isGreatest_bounded_pairing"),
                H("Spectral sharpness is the greatest bounded spectral pairing"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsGreatest")), Open,
                    Left, OpenBrace,
                    F.Id("C"), Underscore, F.Id("a"), Open, F.Id("r"), Close,
                    Sp, Mid, Sp, Forall, Sp, F.Id("i"), Comma, Sp,
                    Lvert, Sp, F.Id("a"), Underscore, F.Id("i"), Sp, Rvert,
                    Sp, Le, Sp, D(1),
                    Right, CloseBrace, Comma, Esc,
                    Operatorname, Grp(F.Id("sharp")), Open, F.Id("r"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite real spectrum r, consider every real observable a whose "
                        + "coordinates have absolute value at most one. The spectral sharpness "
                        + "sharp(r) is a value attained by the spectral pairing capacity C_a(r), "
                        + "and every such bounded pairing is at most sharp(r). Thus sharp(r) is "
                        + "the greatest member of the set of attained bounded-pairing values.")),
                    Paragraph(Text(
                        "Reindexing the reversed half of the pairing expresses C_a(r) as one "
                        + "half the sum of (r_i - r_{rev i}) a_i. The coordinatewise sign of "
                        + "r_i - r_{rev i} is a plus-or-minus-one witness and turns every term "
                        + "into its absolute value, proving attainment. For an arbitrary bounded "
                        + "a, the triangle inequality and |a_i| <= 1 give the matching upper bound.")),
                    Paragraph(Text(
                        "This statement closes only the variational-duality and sign-witness "
                        + "subclaim of the source clause. It does not claim the qubit reduction, "
                        + "the zero-sharpness characterization, the saturation criterion, or "
                        + "data-processing monotonicity."))),
                DescribeRole.Theorem))));
}
