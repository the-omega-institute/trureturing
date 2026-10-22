using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockRetainedEnergyFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full retained creation-energy factorization", H("Retained Gaussian Factorization"), Blocks(
            Paragraph(Text("D is the unrestricted original lattice datum, and a,b range over its full integral charge group. "
                + "The output charge is a+b; arbitrary output charge c is obtained by b=c-a. "
                + "No positivity, rank restriction, occupation cutoff, or nonzero target coefficient is assumed. "
                + "G is the actual energy scalar already identified with chargedEnergyGaussian. "
                + "All retained oscillator variables and the distinguished shift variable remain independent.")),
            Describe.Lean(DescribeId.Create("actual-retained-energy-gaussian-factorization"),
                DeclarationHandle.Create(Prefix + "actual_retained_energy_gaussian_factorization"),
                H("Full Polynomial Gaussian"),
                StatementSource.FromAuthor(Disp(Call("RetainedEnergyGaussianFactorization", F.Id("D"),
                    F.Id("a"), F.Id("b"), F.Id("e")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The e-th original corrected creation coefficient equals the e-th coefficient of "
                    + "the normal creation exponential, renamed into X(some i), times the scalar-energy series "
                    + "with its e-th coefficient multiplied by X(none)^e. The scalar recurrence is reused, "
                    + "not re-proved or promoted from a vacuum projection. The derivative of the product "
                    + "has the full retained polynomial convolution derived from actual contraction and insertion. "
                    + "Strong induction and the genuine original coefficient F_0=1 identify the complete coefficients. "
                    + "The scalar-only statement cannot replace this full polynomial equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-retained-energy-finite-gaussian"),
                DeclarationHandle.Create(Prefix + "actual_retained_energy_finite_gaussian"),
                H("Exact Finite Normal-Energy Expansion"),
                StatementSource.FromAuthor(Disp(Call("RetainedEnergyFiniteGaussian", F.Id("D"),
                    F.Id("a"), F.Id("b"), F.Id("e")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every e, the retained polynomial is the finite sum over 0<=n<=e of "
                    + "rename(some,creationCoeff(a,n)) times C(coeff(e-n,chargedEnergyGaussian(a,b))) "
                    + "times X(none)^(e-n). This keeps every normal frequency, repeated variable and shift. "
                    + "The original singleton and ordered-pair contributions enter G exactly once. "
                    + "Applying the existing native correction evaluation gives equality of the original fields "
                    + "and hence of every integer mode on an arbitrary actual target tensor, by finite linearity. "
                    + "This does not yet prove the regular charged-product scalar ratio, the two-sheet substitution, "
                    + "the complete Lambda/J jet comparison, or either original charged all-j endpoint."))),
                DescribeRole.Theorem))));
}
