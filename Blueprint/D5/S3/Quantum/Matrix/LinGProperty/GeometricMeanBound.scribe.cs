using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class GeometricMeanBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The matrix geometric mean dominates a quantitative arithmetic correction.",
        H("Geometric mean lower bound"), Blocks(
        Item("geometricMean", "Geometric mean",
            "For finite complex square matrices P and Q, set geometricMean(P,Q) to the existing inverse-base mean gmInv(P inverse,Q). "
            + "For positive definite inputs this is P^(1/2)(P^(-1/2) Q P^(-1/2))^(1/2)P^(1/2). "
            + "The total definition also assigns zero whenever either input is zero; these are the singular cases needed by the block inequality.", true),
        Item("geometricMean_riccati", "Positive Riccati solution",
            "For every dimension and positive definite P,Q, their geometric mean G is positive definite and satisfies G P inverse G=Q. "
            + "This uses the existing Riccati theorem at base P inverse and supplies positivity and the identity used below."),
        Item("harmonic_le_geometricMean", "Harmonic lower bound",
            "For every positive definite P,Q, the inverse of (P inverse+Q inverse)/2 is at most their geometric mean G in Loewner order. "
            + "The Riccati equation gives G inverse P G inverse=Q inverse. The positive quadratic form "
            + "(G inverse−P inverse) P (G inverse−P inverse) equals P inverse+Q inverse−2G inverse. "
            + "Inverse order then gives the asserted comparison without a commutation assumption."),
        Item("harmonic_eq_arithmetic_correction", "Exact arithmetic correction",
            "For H=(P+Q)/2 and K=(P−Q)/2 with P,Q positive definite, the harmonic mean is exactly H−K H inverse K. "
            + "The intermediate expression P H inverse Q has inverse Q inverse H P inverse=(P inverse+Q inverse)/2. "
            + "Expanding P=H+K and Q=H−K preserves the order of all matrix factors."),
        Item("arithmetic_sub_le_geometricMean", "Quantitative lower bound",
            "For every dimension, positive definite P,Q and real c,d with c>0, put H=(P+Q)/2 and K=(P−Q)/2. "
            + "If cI≤H and K²≤dI, then H−(d/c)I≤geometricMean(P,Q). "
            + "Inverse order yields H inverse≤I/c; conjugation by Hermitian K and the square bound give K H inverse K≤(d/c)I. "
            + "The exact harmonic correction and harmonic lower bound complete the argument. "
            + "Taking d to be the squared operator norm of K recovers the corresponding operator norm estimate."),
        Item("geometricMean_smul", "Independent positive scaling",
            "For every positive definite P,Q and positive real r,s, geometricMean(rP,sQ)=sqrt(rs) geometricMean(P,Q). "
            + "The scaled matrix is positive definite and satisfies the scaled Riccati equation, so uniqueness identifies the two means. "
            + "This identity restores arbitrary diagonal traces after normalization."),
        Item("geometricMean_zero_right", "Zero second input",
            "For every complex square matrix P, geometricMean(P,0)=0. This includes every dimension and supplies the zero-block branch."),
        Item("geometricMean_zero_left", "Zero first input",
            "For every complex square matrix Q, geometricMean(0,Q)=0. This includes every dimension and supplies the other zero-block branch."))));

    private static DocumentBlock Item(string name, string title, string explanation, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
