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
                H("Finite Gram positivity at the boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let mu be a positive measure on the real line such that exp(-sigma*y) "
                    + "is integrable for every sigma>0. Fix a finite family of frequencies "
                    + "t(j), and suppose the limit L(t(j)-t(k)) of sigma times the Laplace "
                    + "transform at sigma+i*(t(j)-t(k)) exists at each pairwise difference. "
                    + "For complex coefficients a(j), the double sum "
                    + "a(j)*conjugate(a(k))*L(t(j)-t(k)) is a nonnegative real number. "
                    + "This is the finite Gram positivity of the positive measure carried to "
                    + "boundary limits, as in step (a) of Proposition 486.1: characters give "
                    + "rank-one Gram matrices, integration preserves positivity, and the boundary "
                    + "limit preserves each finite matrix inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-sign-budget"),
                DeclarationHandle.Create(Prefix + "same_sign_budget"),
                H("A budget for negative boundary masses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let t(1),...,t(n) be distinct nonzero frequencies. Suppose boundary limits "
                    + "exist at all pairwise differences of 0,t(1),...,t(n), and Re(L(u))<=0 "
                    + "at each nonzero such difference u. Suppose Re(L(t(j)))<=-c with c>0. "
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
                    "Let t(1),...,t(n) be a distinct finite family with abs(t(j)-t(k))<delta. "
                    + "Suppose boundary limits exist at all pairwise differences of "
                    + "0,t(1),...,t(n), and L(u)=0 at each such difference with 0<abs(u)<delta. "
                    + "Then the sum of abs(L(t(j)))^2 is at most "
                    + "L(0)^2. In particular the conclusion applies in every interval of length "
                    + "less than delta. The off-diagonal entries vanish. Test the augmented "
                    + "matrix with the coefficient L(0) at zero and -conjugate(L(t(j))) at "
                    + "the other frequencies; when L(0)=0, use coefficient one at zero."))),
                DescribeRole.Theorem))));
}
