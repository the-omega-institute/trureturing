using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical Dirichlet completion estimates from Euler integrals and reflection.",
        H("Dirichlet completions"),
        Blocks(
            Paragraph(Text(
                "The normalization and functional equation are classical Dirichlet L-function "
                + "theory, as treated in Davenport, Multiplicative Number Theory. The Gamma "
                + "estimates use Euler integrals and Bohr-Mollerup convexity.")),
            Describe.Lean(DescribeId.Create("entire-completion"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.differentiable_completion"),
                H("Entire nonprincipal completions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive integer q and nonprincipal complex Dirichlet "
                    + "character chi modulo q, the function Fchi(s) = exp((log(q)/2)s) "
                    + "completedLFunction(chi,s) is complex differentiable everywhere. "
                    + "Primitivity is unnecessary. The exponential factor is entire and never "
                    + "zero; Mathlib supplies the entire continuation of the nonprincipal "
                    + "completed L-function. The completion and Gamma identities are "
                    + "classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-equation"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_one_sub"),
                H("The normalized functional equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q, every primitive complex character chi "
                    + "modulo q and every complex s, Fchi(1-s) = rootNumber(chi) "
                    + "FchiInverse(s). Nonprincipality is unnecessary. Mathlib gives the "
                    + "classical Dirichlet functional equation with the factor q to the power "
                    + "s minus one half. Combining the two real-logarithm exponential factors "
                    + "cancels that power. The normalization and equation are classical "
                    + "results of Dirichlet L-function theory. The completion and Gamma "
                    + "identities are classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_ne_zero_of_one_le_re"),
                H("The closed right half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q, character chi and complex s with Re(s) "
                    + "at least one, Fchi(s) is nonzero provided chi is nonprincipal or s is "
                    + "not one. The character need not be primitive. Mathlib supplies "
                    + "nonvanishing of L(chi,s) on this closed half-plane. The identity L = "
                    + "completedLFunction / gammaFactor then forces the numerator to be "
                    + "nonzero, and multiplication by an exponential preserves nonvanishing. "
                    + "The exception retains the principal pole and the totalized values used "
                    + "by the analytic continuation. The completion and Gamma identities are "
                    + "classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.rootNumber_ne_zero"),
                H("A nonzero root number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every primitive complex Dirichlet character of positive modulus, "
                    + "rootNumber(chi) is nonzero. Apply the normalized functional equation "
                    + "at s = -1. Its left side is Fchi(2), which is nonzero by right "
                    + "half-plane nonvanishing. No nonprincipal or prime-modulus hypothesis "
                    + "is imposed. The completion and Gamma identities are classical analytic "
                    + "number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_ne_zero_of_re_le_zero"),
                H("The closed left half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "If chi is primitive and nonprincipal of positive modulus, Fchi(s) is "
                    + "nonzero whenever Re(s) is at most zero. Reflection sends s to 1-s in "
                    + "the closed right half-plane. The inverse character is nonprincipal, "
                    + "and the root number is nonzero. Consequently every zero of Fchi has "
                    + "real part strictly between zero and one. The completion and Gamma "
                    + "identities are classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjugate-completion"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_inv_conj"),
                H("Conjugation and inversion of a character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every nonprincipal complex Dirichlet character chi of positive "
                    + "modulus and every complex s, FchiInverse(conjugate(s)) = "
                    + "conjugate(Fchi(s)). Primitivity is unnecessary. Conjugation equals "
                    + "inversion on the finite-order nonzero character values. Termwise "
                    + "conjugation of the absolutely convergent Dirichlet series proves the "
                    + "identity on Re(s)>1. The real archimedean factor commutes with "
                    + "conjugation, and conjugating both the input and output preserves "
                    + "holomorphy. The identity principle extends the equality everywhere. "
                    + "The completion and Gamma identities are classical analytic number "
                    + "theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-root-number"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.norm_rootNumber"),
                H("Unit norm for every primitive root number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Every primitive complex Dirichlet character of positive modulus "
                    + "satisfies norm(rootNumber(chi)) = 1. For a nonprincipal character, "
                    + "evaluate the normalized functional equation at two and minus one and "
                    + "take norms. Conjugation identifies the norms for the character and its "
                    + "inverse at these real arguments. Nonvanishing at minus one allows "
                    + "cancellation, so the square of the root-number norm is one. If the "
                    + "primitive character is principal its modulus is one, and Mathlib gives "
                    + "rootNumber = 1. The completion and Gamma identities are classical "
                    + "analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("explicit-global-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_growth_explicit"),
                H("A radial Gamma bound on the whole plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Let q be positive and let chi be primitive and nonprincipal. Put B = "
                    + "max(1,Gamma(1/4)), R = 1 + norm(s), and U = (R+3)/2. For every complex "
                    + "s, norm(Fchi(s)) < B phi(q) R exp((log(q)/2)R + U log(U)). On Re(s) at "
                    + "least one half, the strict nonprincipal L-function bound gives "
                    + "norm(L(chi,s)) < phi(q) norm(s). The real part of the Gamma argument "
                    + "is at least one quarter, and its real argument plus one is at most U "
                    + "whenever norm(s) is bounded by R. The factor involving pi is at most "
                    + "one. On the other half-plane, reflect to 1-s and use the unit norm of "
                    + "the root number. The same R bounds norm(1-s). This estimate concerns "
                    + "all complex arguments and does not assert that the entire function has "
                    + "order exactly one. The completion and Gamma identities are classical "
                    + "analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("logarithmic-global-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_growth_log"),
                H("An explicit logarithmic growth coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "With B = max(1,Gamma(1/4)), set C = max(log(B phi(q)) + log(q)/2 + 2 "
                    + "log(2), 3). For every positive q, primitive nonprincipal chi modulo q "
                    + "and complex s, with R = 1 + norm(s), norm(Fchi(s)) < exp(C R "
                    + "(1+log(R))). Indeed U = (R+3)/2 is at most 2R. Expanding log(2R) and "
                    + "absorbing the positive prefactor gives the displayed coefficient. The "
                    + "elementary inequality 1+log(R) <= 2 sqrt(R), valid for R at least one, "
                    + "also gives norm(Fchi(s)) <= exp(2 C R to the power 3/2). Thus the "
                    + "exponent 3/2 is available for the two-point logarithmic derivative "
                    + "formula for entire functions with growth below a quadratic exponent. "
                    + "This is a consequence of the logarithmic estimate. The completion and "
                    + "Gamma identities are classical analytic number theory."))),
                DescribeRole.Theorem))));
}
