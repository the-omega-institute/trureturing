using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class SpectralSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral sharpness vanishes exactly on the uniform spectrum.",
        H("Zero Spectral Sharpness Characterises the Uniform Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-sharpness-zero-iff-uniform"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/SpectralSharpness.spectral_sharpness_zero_iff_uniform"),
                H("Spectral sharpness is zero iff the spectrum is uniform"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("sharp")), Open, F.Id("r"), Close, Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Sum, Underscore, F.Id("i"), Sp,
                    Lvert, Sp, F.Id("r"), Underscore, F.Id("i"), Sp, Minus, Sp,
                    F.Id("r"), Underscore, Grp(Operatorname, Grp(F.Id("rev")), Sp, F.Id("i")),
                    Rvert, RowBreak,
                    Operatorname, Grp(F.Id("sharp")), Open, F.Id("r"), Close, Sp, Eq, Sp, D(0), Sp,
                    Iff, Sp, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("r"), Underscore, F.Id("i"), Sp, Eq, Sp, Frac, Grp(D(1)), Grp(F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The spectral sharpness of a spectrum r is the total variation between the "
                        + "spectrum and its reversal, sharp(r) = (1/2) sum_i |r_i - r_{rev i}|, "
                        + "equivalently half the L1 distance. For an antitone unit-sum spectrum on n "
                        + "points — a nonincreasing real vector summing to one, in particular any sorted "
                        + "probability spectrum, though nonnegativity is not needed — the sharpness "
                        + "vanishes exactly when the spectrum is uniform, that is r_i = 1/n for every i.")),
                    Paragraph(Text(
                        "The summands of the sharpness are nonnegative, so a zero sharpness forces each "
                        + "|r_i - r_{rev i}| to vanish and the spectrum to equal its own reversal. In "
                        + "particular the first and last entries agree, and antitonicity squeezes every "
                        + "entry between these two equal values, so the spectrum is constant; the unit sum "
                        + "then pins that constant to 1/n. The converse is immediate, since a uniform "
                        + "spectrum equals its reversal and every summand vanishes.")),
                    Paragraph(Text(
                        "This is the faithful-freedom-radius clause of the maximal-sharpness law: only "
                        + "the characterisation sharp(r) = 0 iff uniform is claimed here. The companion "
                        + "clauses of that law — the variational supremum realising the sharpness, the "
                        + "median-cut plus-or-minus-one witness, the qubit reduction to the Bloch radius, "
                        + "the full-rank saturation criterion for sharpness one, and the data-processing "
                        + "monotonicity of the sharpness — are not covered by this statement."))),
                DescribeRole.Theorem))));
}
