using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class OffLineToySpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four explicit off-line points retain mirror and polynomial symmetries, while their "
        + "thirty-first Li coefficient has negative real part.",
        H("Off-Line Toy Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-toy-spectrum-has-four-points"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.toy_spectrum_cardinality"),
                H("The toy spectrum has four points"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lvert, Sp, Operatorname, Grp(F.Id("toySpectrum")), Sp, Rvert,
                    Sp, Eq, Sp, D(4)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The spectrum consists of the four distinct complex numbers "
                        + "7/10 + 5i, 7/10 - 5i, 3/10 + 5i, and 3/10 - 5i. This "
                        + "cardinality certificate rules out collapse or vacuity in the "
                        + "subsequent universal statements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mirror-invariance-does-not-force-fixed-points"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/OffLineToySpectrum."
                    + "explicit_off_line_j_invariant_four_point_counterexample"),
                H("Mirror invariance does not force fixed points"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("s"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("toySpectrum")), Comma, Esc,
                    Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close,
                    Sp, InMacro, Sp, Operatorname, Grp(F.Id("toySpectrum")), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("s"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("toySpectrum")), Comma, Esc,
                    Re, Open, F.Id("s"), Close, Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("criticalAbscissa")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every point s in the four-point spectrum, the repository's "
                        + "frozen mirror mirror(s) = 1 - conjugate(s) is also in the "
                        + "spectrum. Every one of the four real parts is nevertheless "
                        + "different from the critical abscissa 1/2.")),
                    Paragraph(Text(
                        "In particular, setwise invariance under the frozen involution does "
                        + "not imply that the set is contained in its fixed locus. No second "
                        + "reflection or involution is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-formal-polynomial-symmetries-hold"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/OffLineToySpectrum."
                    + "toy_spectrum_satisfies_formal_polynomial_symmetries"),
                H("The formal polynomial symmetries hold"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Monic")), Open,
                    Operatorname, Grp(F.Id("toyQuartic")), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, Rho, Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("toySpectrum")), Comma, Esc,
                    Operatorname, Grp(F.Id("eval")), Open,
                    Operatorname, Grp(F.Id("toyQuartic")), Comma, Sp, Rho, Close,
                    Sp, Eq, Sp, D(0), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("s"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Operatorname, Grp(F.Id("eval")), Open,
                    Operatorname, Grp(F.Id("toyQuartic")), Comma, Sp,
                    D(1), Sp, Minus, Sp, F.Id("s"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("eval")), Open,
                    Operatorname, Grp(F.Id("toyQuartic")), Comma, Sp,
                    F.Id("s"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("s"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Operatorname, Grp(F.Id("eval")), Open,
                    Operatorname, Grp(F.Id("toyQuartic")), Comma, Sp,
                    Overline, Grp(F.Id("s")), Close,
                    Sp, Eq, Sp,
                    Overline, Grp(Operatorname, Grp(F.Id("eval")), Open,
                        Operatorname, Grp(F.Id("toyQuartic")), Comma, Sp,
                        F.Id("s"), Close), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The monic quartic is the product of X minus each of the four "
                        + "displayed points. Every point in the spectrum is a root, and its "
                        + "evaluation obeys F(1 - s) = F(s) and "
                        + "F(conjugate(s)) = conjugate(F(s)) for every complex s.")),
                    Paragraph(Text(
                        "This is an honest partial formalization of the source's five-property "
                        + "toy-spectrum certificate. The repository provides no D5 definitions "
                        + "for antiunitary covariance or information complementarity, so those "
                        + "two clauses are not encoded or claimed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-thirty-first-li-coefficient-is-negative"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/OffLineToySpectrum."
                    + "li_positivity_distinguishes_the_off_line_toy_spectrum"),
                H("The thirty-first Li coefficient is negative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Re, Open,
                    Sum, Underscore, Grp(Rho, Sp, InMacro, Sp,
                        Operatorname, Grp(F.Id("toySpectrum"))), Sp,
                    Open, D(1), Sp, Minus, Sp,
                    Open, D(1), Sp, Minus, Sp,
                    Frac, Grp(D(1)), Grp(Rho), Close,
                    Caret, Grp(D(3, 1)), Close,
                    Close, Sp, Lt, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the explicit four-point spectrum, the real part of the finite "
                        + "sum of 1 - (1 - 1/rho)^31 is strictly negative. Lean checks the "
                        + "fixed exponent and all four rational complex terms exactly.")),
                    Paragraph(Text(
                        "The theorem states only this concrete n = 31 computation. It does not "
                        + "assert a general Li criterion, positivity equivalence, or a claim "
                        + "about every small index."))),
                DescribeRole.Theorem)),
        []));
}
