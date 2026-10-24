using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class TwoBlockDefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two parameter blocks in the generalized hypergeometric Turanian.",
        H("The coefficient assertion of Conjecture 2"), Blocks(
            Entry("unshifted-pochhammer-ratio", "pochRatio", "The unshifted parameter block",
                "For parameter vectors a1 and b1 and natural n, pochRatio is the product of (ascPochhammer R n).eval a1(i) divided by the corresponding product for b1. These are the rising factorials in the unshifted block of equation (3). Empty products equal one."),
            Entry("two-block-taylor-coefficient", "seriesCoeff", "The Taylor coefficient in equation (3)",
                "Equation (3) on page 2 defines f(mu;x)=Gamma(a2+mu)/Gamma(b2+mu) times pFq(a1,a2+mu;b1,b2+mu;x). Its degree n Taylor coefficient is pochRatio(a1,b1,n) times Defs.coeff(a2,b2,mu+n), divided by n!. Thus the shifted Gamma product includes the numerator block a2, while the rising factorial ratio contains only the unshifted block."),
            Entry("two-block-turanian-coefficient", "twoBlockTuranCoeff", "The Cauchy coefficient",
                "For natural m, sum F(k,mu+alpha)F(m-k,mu+beta)-F(k,mu)F(m-k,mu+alpha+beta) over k from zero through m, where F(n,t) is seriesCoeff at t and n. The factorials are already included in F. This is the coefficient of x to the power m in equation (2), the generalized Turanian of equation (3). The subtraction m-k is natural subtraction, and k is at most m in this sum."),
            Entry("conjecture-two-coefficient-claim", "claim", "Universal coefficient nonnegativity",
                "Conjecture 2 on page 6 states: ‘Conjecture 2. Suppose p1 ≤ q1 , p2 ≤ q2 and conditions (13) hold for a1 , b1 and a2 , b2 . Then the function µ → f (µ; x) defined in (3) is log-concave on [1, ∞) and the corresponding generalized Turánian ∆f (α, β; x) has nonnegative coefficients at all powers of x.’ The standing assumption on page 2 is: ‘We will always assume that a2 is not empty (i.e. p2 ≥ 1), while all other subvectors are allowed to be empty.’ The definition encodes the coefficient clause: p1 is at most q1, p2 is at least one and at most q2, all four parameter vectors are positive, and Defs.cond13 holds separately for both blocks. For every mu at least one, every nonnegative alpha and beta, and every natural m, require twoBlockTuranCoeff to be nonnegative. There is no additional relation between alpha and beta. Refuting this clause requires no assertion about log-concavity of the function for a fixed x."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
