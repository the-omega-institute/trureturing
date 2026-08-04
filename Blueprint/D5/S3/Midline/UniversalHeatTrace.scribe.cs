using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class UniversalHeatTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/UniversalHeatTrace",
            "The abscissa of a nonnegative heat trace canonically determines its l2, resonance, and half-density midline."),
        H("The Universal Heat-Trace Midline"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("heat-coefficients-have-the-half-abscissa-boundary"),
                H("Heat coefficients have the half-abscissa boundary"),
                LeanTheorem(
                    "D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff"),
                LatexStatement.Create(@"$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M:A\to\mathbb{R},\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\sigma\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\sigma M(a)})\Leftrightarrow\alpha<\sigma\\ \Rightarrow\quad \operatorname{MemLp}(a\mapsto e^{-sM(a)},2)\Leftrightarrow\frac{\alpha}{2}<\Re(s). \end{gathered}$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The abscissa alpha is characterized by the displayed summability equivalence; it is not constructed in this module. Squaring coordinate norms doubles the real parameter, so square summability begins exactly to the right of alpha over two.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("norm-square-is-the-vertical-invariant-heat-trace"),
                H("Norm square is the vertical-invariant heat trace"),
                LeanTheorem(
                    "D5/S3/Midline/UniversalHeatTrace.heat_vector_norm_sq"),
                LatexStatement.Create(@"$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\rho\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\rho M(a)})\Leftrightarrow\alpha<\rho,\quad \frac{\alpha}{2}<\sigma\\ \Rightarrow\quad \left\Vert\mathbf{Z}_{M}(\sigma+it)\right\Vert^{2}=D_M(2\sigma)=\sum_{a\in A}e^{-2\sigma M(a)}. \end{gathered}$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every vertical parameter t, the squared lp norm is the same heat trace at twice sigma. Thus imaginary translation changes phases but not the norm.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-source-pairing-is-the-heat-kernel"),
                H("The source pairing is the heat kernel"),
                LeanTheorem(
                    "D5/S3/Midline/UniversalHeatTrace.heat_vector_inner"),
                LatexStatement.Create(@"$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\rho\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\rho M(a)})\Leftrightarrow\alpha<\rho,\quad \frac{\alpha}{2}<\Re(s),\ \frac{\alpha}{2}<\Re(w)\\ \Rightarrow\quad \left\langle\mathbf{Z}_{M}(s),\mathbf{Z}_{M}(w)\right\rangle=D_M(s+\overline{w}). \end{gathered}$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source-ordered inner product is the heat trace at s plus conjugate w. In this module resonance names the affine equation s plus conjugate w equals alpha; it does not assert meromorphic continuation or the existence of a pole.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("resonance-and-half-density-select-the-same-midline"),
                H("Resonance and half-density select the same midline"),
                LeanTheorem(
                    "D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline"),
                LatexStatement.Create(@"$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M:A\to\mathbb{R},\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\ 0<\alpha,\\ \forall\sigma\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\sigma M(a)})\Leftrightarrow\alpha<\sigma\\ \Rightarrow\quad \left[\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)\Leftrightarrow\frac{\alpha}{2}<\Re(s)\right],\\ \left[s+\overline{s}=\alpha\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right],\\ \left[(\forall a,\ |e^{\alpha M(a)/2}e^{-sM(a)}|=1)\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right]. \end{gathered}$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The square-summability boundary, self-resonance line, and coordinatewise unit-modulus half-density line all equal alpha over two. This free triple coincidence uses no functional equation. The companion resonance theorem also derives the unique partner w = alpha - conjugate s and proves that this partner map is an involution.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("reflection-center-equals-the-abscissa"),
                H("Reflection center equals the abscissa"),
                LeanTheorem(
                    "D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff"),
                LatexStatement.Create(@"$$\forall\alpha,c\in\mathbb{R},\quad \left[\forall s\in\mathbb{C},\ s=c-\overline{s}\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right]\Leftrightarrow c=\alpha.$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A separately supplied reflection s maps to c minus conjugate s has the universal heat-trace midline as its fixed line exactly when its center c is the heat-trace abscissa alpha.")))
            ))));
}
