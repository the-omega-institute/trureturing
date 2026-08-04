using static StrataLint.Scribe.DefinitionDsl;

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
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \frac{1}{2}<\Re(s) \Rightarrow \operatorname{ofReal}(\Vert\operatorname{labeledZetaVector}(s)\Vert^{2})=\operatorname{classicalZeta}(2\Re(s))$"),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "When the real part of the parameter is greater than one half, the squared lp norm of the labeled zeta vector is the classical zeta function evaluated at twice that real part. The right side is independent of the imaginary part. No numerical window certificate is promoted into this exact identity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-membership-has-the-half-density-boundary"),
                H("Labeled zeta membership has the half-density boundary"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff"),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2) \Leftrightarrow \frac{1}{2}<\Re(s)$"),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The raw labeled coefficient function is square-summable exactly when the spectral parameter has real part greater than one half. Its proof specializes the universal heat-abscissa theorem to PrimeAxisTable with logarithmic length and alpha equal to one, so this instance is downstream of the general theorem rather than a parallel derivation. The boundary divergence used here is proved from the harmonic series.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("coefficient-pairing-is-the-zeta-kernel"),
                H("The coefficient pairing is the zeta kernel"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel"),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ 1<\Re(s+\overline{w}) \Rightarrow \sum_{a\in\operatorname{PrimeAxisTable}}\operatorname{labeledZetaCoefficient}(s,a)\overline{\operatorname{labeledZetaCoefficient}(w,a)}=\operatorname{classicalZeta}(s+\overline{w})$$"),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "If the real part of s plus the conjugate of w is greater than one, the raw coefficient pairing sums to the classical zeta function at that parameter. This series theorem keeps only the joint convergence hypothesis and does not add individual square-summability assumptions.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("hilbert-pairing-is-the-zeta-kernel"),
                H("The Hilbert pairing is the zeta kernel"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner"),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ \frac{1}{2}<\Re(s) \land \frac{1}{2}<\Re(w) \Rightarrow \operatorname{sourcePairing}(\operatorname{labeledZetaVector}(s),\operatorname{labeledZetaVector}(w))=\operatorname{classicalZeta}(s+\overline{w})$$"),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "For two actual labeled vectors in the square-summable half-plane, the source-ordered Hilbert pairing is the same zeta kernel. The two individual half-plane hypotheses are typing conditions for the vectors; they imply the raw kernel's joint convergence condition.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("mirror-is-the-unique-resonance-partner"),
                H("The mirror is the unique resonance partner"),
                LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.resonance_partner_spec"),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ (s+\overline{w}=1 \Leftrightarrow w=1-\overline{s}) \land (s+\overline{s}=1 \Leftrightarrow \Re(s)=\frac{1}{2}) \land (\frac{1}{2}<\Re(s) \Rightarrow \Re(1-\overline{s})<\frac{1}{2})$$"),
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
            ))));
}
