using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class PositiveSpectralBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/PositiveSpectralBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary limits of a positive Laplace transform obey finite Gram inequalities and spectral budgets.",
        H("Positive Laplace boundary kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-limit-conjugate"),
                DeclarationHandle.Create(Prefix + "boundary_limit_conjugate"),
                H("Conjugate boundary limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive measure on the real line, the Laplace transform at sigma-i*t "
                    + "is the conjugate of its value at sigma+i*t. Consequently, if sigma times "
                    + "the latter transform has a limit as sigma decreases to zero, the opposite "
                    + "frequency also has a limit, equal to the complex conjugate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-positive-definite"),
                DeclarationHandle.Create(Prefix + "boundary_positive_definite"),
                H("Positive definiteness of boundary limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let mu be a positive measure on the real line such that exp(-sigma*y) "
                    + "is integrable for every sigma>0. Fix a finite family of frequencies "
                    + "t(j), and suppose the limit L(t(j)-t(k)) of sigma times the Laplace "
                    + "transform at sigma+i*(t(j)-t(k)) exists at each pairwise difference. "
                    + "For complex coefficients a(j), the double sum "
                    + "a(j)*conjugate(a(k))*L(t(j)-t(k)) is a nonnegative real number. "
                    + "Characters give rank-one Gram matrices, integration preserves positivity, "
                    + "and the boundary limit preserves each finite matrix inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-conjugate"),
                DeclarationHandle.Create(Prefix + "boundary_conjugate"),
                H("Hermitian symmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Whenever all boundary values exist, L(-t)=conjugate(L(t))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-zero-nonnegative"),
                DeclarationHandle.Create(Prefix + "boundary_zero_nonnegative"),
                H("The diagonal mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the integrability and boundary-limit assumptions, L(0) is a nonnegative real number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-sign-budget"),
                DeclarationHandle.Create(Prefix + "same_sign_budget"),
                H("A budget for negative boundary masses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose every nonzero boundary frequency has nonpositive real part. "
                    + "At n distinct nonzero frequencies suppose Re(L(t(j)))<=-c with c>0. "
                    + "Then n*c^2<=4*L(0)^2. Apply the finite Gram inequality to the augmented "
                    + "family 0,t(1),...,t(n), with a real nonnegative coefficient s at zero "
                    + "and coefficient one elsewhere, and optimize the resulting quadratic inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gap-budget"),
                DeclarationHandle.Create(Prefix + "gap_budget"),
                H("A quadratic budget in a short window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose delta>0 and L(t)=0 for 0<abs(t)<delta. For any distinct finite "
                    + "family with abs(t(j)-t(k))<delta, the sum of abs(L(t(j)))^2 is at most "
                    + "L(0)^2. In particular the conclusion applies in every interval of length "
                    + "less than delta. The off-diagonal entries vanish. Test the augmented "
                    + "matrix with the coefficient L(0) at zero and -conjugate(L(t(j))) at "
                    + "the other frequencies; when L(0)=0, use coefficient one at zero."))),
                DescribeRole.Theorem))));
}
