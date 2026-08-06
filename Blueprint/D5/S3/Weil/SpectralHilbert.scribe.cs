using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class SpectralHilbertDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef HedenmalmHilbert =
        LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/SpectralHilbert",
            "The square-summable zeta coefficient geometry supplies a spectral foundation for Weil positivity."),
        H("The Spectral Hilbert Foundation"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("source-pairing-completes-the-coefficient-space"),
                H("The source pairing completes the coefficient space"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum"),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The coefficient space is the square-summable complex lp space indexed by the canonical prime-axis table. Its source pairing is linear in the first displayed coefficient and conjugate-linear in the second, so it is defined by reversing mathlib's inner-product arguments. The subtype coercion supplies the inclusion into the unrestricted coefficient product.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-norm-is-zeta-on-the-convergence-side"),
                H("The labeled zeta norm is zeta on the convergence side"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq"),
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("ofReal")), Open, Vert, Operatorname, Grp(F.Id("labeledZetaVector")), Open, F.Id("s"), Close, Vert, Caret, Grp(D(2)), Close, Eq, Operatorname, Grp(F.Id("classicalZeta")), Open, D(2), Re, Open, F.Id("s"), Close, Close)),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "When the real part of the parameter is greater than one half, the squared lp norm of the labeled zeta vector is the classical zeta function evaluated at twice that real part. The right side is independent of the imaginary part. No numerical window certificate is promoted into this exact identity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-membership-has-the-half-density-boundary"),
                H("Labeled zeta membership has the half-density boundary"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff"),
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Operatorname, Grp(F.Id("MemLp")), Open, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Close, Comma, D(2), Close, Sp, Leftrightarrow, Sp, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close)),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The raw labeled coefficient function is square-summable exactly when the spectral parameter has real part greater than one half. Thus the reverse implication includes every parameter on or to the left of the boundary; the statement does not replace that exact p-series criterion by a separate pole or Euler-product claim.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("coefficient-pairing-is-the-zeta-kernel"),
                H("The coefficient pairing is the zeta kernel"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel"),
                Disp(Seq(Forall, Sp, F.Id("s"), Comma, F.Id("w"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, D(1), Lt, Re, Open, F.Id("s"), Plus, Overline, Grp(F.Id("w")), Close, Sp, Rightarrow, Sp, Sum, Underscore, Grp(F.Id("a"), InMacro, Operatorname, Grp(F.Id("PrimeAxisTable"))), Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Comma, F.Id("a"), Close, Overline, Grp(Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("w"), Comma, F.Id("a"), Close), Eq, Operatorname, Grp(F.Id("classicalZeta")), Open, F.Id("s"), Plus, Overline, Grp(F.Id("w")), Close)),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "If the real part of s plus the conjugate of w is greater than one, the raw coefficient pairing sums to the classical zeta function at that parameter. This series theorem keeps only the joint convergence hypothesis and does not add individual square-summability assumptions.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("hilbert-pairing-is-the-zeta-kernel"),
                H("The Hilbert pairing is the zeta kernel"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner"),
                Disp(Seq(Forall, Sp, F.Id("s"), Comma, F.Id("w"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close, Sp, Land, Sp, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("w"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("sourcePairing")), Open, Operatorname, Grp(F.Id("labeledZetaVector")), Open, F.Id("s"), Close, Comma, Operatorname, Grp(F.Id("labeledZetaVector")), Open, F.Id("w"), Close, Close, Eq, Operatorname, Grp(F.Id("classicalZeta")), Open, F.Id("s"), Plus, Overline, Grp(F.Id("w")), Close)),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "For two actual labeled vectors in the square-summable half-plane, the source-ordered Hilbert pairing is the same zeta kernel. The two individual half-plane hypotheses are typing conditions for the vectors; they imply the raw kernel's joint convergence condition.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("mirror-is-the-unique-resonance-partner"),
                H("The mirror is the unique resonance partner"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.resonance_partner_spec"),
                Disp(Seq(Forall, Sp, F.Id("s"), Comma, F.Id("w"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, F.Id("s"), Plus, Overline, Grp(F.Id("w")), Eq, D(1), Sp, Leftrightarrow, Sp, F.Id("w"), Eq, D(1), Minus, Overline, Grp(F.Id("s")), Close, Sp, Land, Sp, Open, F.Id("s"), Plus, Overline, Grp(F.Id("s")), Eq, D(1), Sp, Leftrightarrow, Sp, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close, Sp, Land, Sp, Open, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Re, Open, D(1), Minus, Overline, Grp(F.Id("s")), Close, Lt, Frac, Grp(D(1)), Grp(D(2)), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The equation s plus conjugate w equals one holds exactly for the mirror partner w = 1 - conjugate s. Self-resonance is exactly the critical line, and a parameter on the square-summable side has its mirror strictly outside that side. This is algebra of the kernel's pole-locus equation; it asserts neither meromorphic continuation nor any location of zeta zeros.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("hardy-space-identification"),
                H("Hardy-space identification"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The coefficient Hilbert space and its zeta reproducing kernel are the classical Hardy-space geometry of Dirichlet series. The repository supplies a typed translation and combined presentation of that known mathematics, not a novelty claim.")))
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Digit/PrimeAxisEncoding")),
                    ]));
}
