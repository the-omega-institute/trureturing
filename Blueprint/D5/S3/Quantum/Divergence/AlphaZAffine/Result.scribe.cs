using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.AlphaZAffine;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/AlphaZAffine/Result.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiai2024affinerenyi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine alpha-z Renyi monotonicity with singular supported inputs", H("Affine alpha-z Renyi monotonicity with singular supported inputs"), Blocks([
            Describe.Lean(DescribeId.Create("affine-z"),
                DeclarationHandle.Create(Prefix + "affineZ"),
                H("Affine scale"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The scale is kappa times alpha plus a nonnegative offset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("renyi-product"),
                DeclarationHandle.Create(Prefix + "renyiProduct"),
                H("The supported power product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The product is rho to alpha over twice z times sigma to one minus alpha over twice z. For nonzero exponents, CFC real powers vanish on the kernel; negative powers therefore invert on the support. At alpha one the sigma exponent is zero and CFC returns the identity; under support inclusion its extra kernel component is killed by the positive rho power. This cancellation concerns the sigma factor at alpha one only."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-moment"),
                DeclarationHandle.Create(Prefix + "traceMoment"),
                H("The singular-value trace moment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The real trace of the z power of X adjoint times X equals the sum of the singular values to power twice z."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("renyi-q"),
                DeclarationHandle.Create(Prefix + "renyiQ"),
                H("The alpha-z trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive alpha and positive z this agrees with the Hiai Section 3 trace functional. The real-valued formula is used on supported semidefinite pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("renyi-d"),
                DeclarationHandle.Create(Prefix + "renyiD"),
                H("The divergence away from one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The logarithm of Q divided by the trace of rho, divided by alpha minus one. Its totalized value at one is unused; hiaiD supplies the Umegaki value there."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("umegaki"),
                DeclarationHandle.Create(Prefix + "umegaki"),
                H("Normalized Umegaki entropy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The real trace of rho times the difference of log rho and log sigma divided by the real trace of rho. Finite spectral logarithms have value zero at zero, which implements the supported convention after multiplication by rho."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hiai-d"),
                DeclarationHandle.Create(Prefix + "hiaiD"),
                H("Hiai divergence including alpha one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For alpha equal to one this is normalized Umegaki entropy. At every other alpha it is the normalized logarithmic trace quotient. Support inclusion is a hypothesis of the theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Affine monotonicity on the full positive axis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In every finite complex matrix dimension, for nonzero positive semidefinite rho and positive semidefinite sigma with kernel sigma contained in kernel rho, positive kappa and nonnegative offset, the divergence along z equals kappa times alpha plus offset is nondecreasing for all positive alpha. The value at one is the prescribed Umegaki entropy. Joint convexity and the constant vertical normalization transfer the Petz tangent to every affine line. Simultaneous positive identity regularization converges in the supported power product: its kernel factor has the positive net exponent one over twice z. The entropy limit uses continuity of x log x and the same kernel cancellation. Passing inequalities through these limits proves the singular case. The Lean conclusion quantifies alpha greater than zero. If the offset is zero, alpha zero gives z zero and lies outside the source domain. If the offset is positive, the source alpha-zero endpoint is defined but is not quantified by result. The positive-alpha rho powers tend to the support projection as alpha decreases to zero. Theorem 3.1 and continuity give the source endpoint comparison: source literature proved or paper derived, not formalized. The totalized CFC rho power at alpha zero is the identity, so the formula there is not asserted to equal the source support-power value. The fixed-z case kappa equals zero is identified as Hiai Theorem 3.1(ii); extended infinite values outside support inclusion are discussed in the source note and are outside this real-valued theorem."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hiai-2024-affine-alpha-z-renyi-monotonicity"),
                    ResolutionKind.Proved))])));
}
