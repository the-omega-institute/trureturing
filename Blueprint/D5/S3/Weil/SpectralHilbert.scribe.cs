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
            new DocumentBlock.Describe(
                DescribeId.Create("source-pairing-completes-the-coefficient-space"),
                DescribeKind.Definition,
                H("The source pairing completes the coefficient space"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The coefficient space is the square-summable complex lp space indexed by the canonical prime-axis table. Its source pairing is linear in the first displayed coefficient and conjugate-linear in the second, so it is defined by reversing mathlib's inner-product arguments. The subtype coercion supplies the inclusion into the unrestricted coefficient product.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("labeled-zeta-norm-is-zeta-on-the-convergence-side"),
                DescribeKind.Theorem,
                H("The labeled zeta norm is zeta on the convergence side"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "When the real part of the parameter is greater than one half, the squared lp norm of the labeled zeta vector is the classical zeta function evaluated at twice that real part. The right side is independent of the imaginary part. No numerical window certificate is promoted into this exact identity."))),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \frac{1}{2}<\Re(s) \Rightarrow \operatorname{ofReal}(\Vert\operatorname{labeledZetaVector}(s)\Vert^{2})=\operatorname{classicalZeta}(2\Re(s))$")),
            new DocumentBlock.Describe(
                DescribeId.Create("labeled-zeta-membership-has-the-half-density-boundary"),
                DescribeKind.Theorem,
                H("Labeled zeta membership has the half-density boundary"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The raw labeled coefficient function is square-summable exactly when the spectral parameter has real part greater than one half. Thus the reverse implication includes every parameter on or to the left of the boundary; the statement does not replace that exact p-series criterion by a separate pole or Euler-product claim."))),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2) \Leftrightarrow \frac{1}{2}<\Re(s)$")),
            new DocumentBlock.Describe(
                DescribeId.Create("coefficient-pairing-is-the-zeta-kernel"),
                DescribeKind.Theorem,
                H("The coefficient pairing is the zeta kernel"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "If the real part of s plus the conjugate of w is greater than one, the raw coefficient pairing sums to the classical zeta function at that parameter. This series theorem keeps only the joint convergence hypothesis and does not add individual square-summability assumptions."))),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ 1<\Re(s+\overline{w}) \Rightarrow \sum_{a\in\operatorname{PrimeAxisTable}}\operatorname{labeledZetaCoefficient}(s,a)\overline{\operatorname{labeledZetaCoefficient}(w,a)}=\operatorname{classicalZeta}(s+\overline{w})$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("hilbert-pairing-is-the-zeta-kernel"),
                DescribeKind.Theorem,
                H("The Hilbert pairing is the zeta kernel"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "For two actual labeled vectors in the square-summable half-plane, the source-ordered Hilbert pairing is the same zeta kernel. The two individual half-plane hypotheses are typing conditions for the vectors; they imply the raw kernel's joint convergence condition."))),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ \frac{1}{2}<\Re(s) \land \frac{1}{2}<\Re(w) \Rightarrow \operatorname{sourcePairing}(\operatorname{labeledZetaVector}(s),\operatorname{labeledZetaVector}(w))=\operatorname{classicalZeta}(s+\overline{w})$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-is-the-unique-resonance-partner"),
                DescribeKind.Theorem,
                H("The mirror is the unique resonance partner"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.resonance_partner_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The equation s plus conjugate w equals one holds exactly for the mirror partner w = 1 - conjugate s. Self-resonance is exactly the critical line, and a parameter on the square-summable side has its mirror strictly outside that side. This is algebra of the kernel's pole-locus equation; it asserts neither meromorphic continuation nor any location of zeta zeros."))),
                LatexStatement.Create(@"$$\forall s,w\in\mathbb{C},\ (s+\overline{w}=1 \Leftrightarrow w=1-\overline{s}) \land (s+\overline{s}=1 \Leftrightarrow \Re(s)=\frac{1}{2}) \land (\frac{1}{2}<\Re(s) \Rightarrow \Re(1-\overline{s})<\frac{1}{2})$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("hardy-space-identification"),
                DescribeKind.Remark,
                H("Hardy-space identification"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner")),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "The coefficient Hilbert space and its zeta reproducing kernel are the classical Hardy-space geometry of Dirichlet series. The repository supplies a typed translation and combined presentation of that known mathematics, not a novelty claim.")))))));
}
