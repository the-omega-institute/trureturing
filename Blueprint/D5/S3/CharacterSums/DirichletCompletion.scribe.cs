using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dirichlet completions, zero multiplicities and explicit vertical resolvents.",
        H("Dirichlet completions and vertical resolvents"),
        Blocks(
            Paragraph(Text(
                "The normalized completion and functional equation belong to classical "
                + "Dirichlet L-function theory, as treated in Davenport, Multiplicative Number "
                + "Theory. The analytic estimates combine the vertical Gamma product, "
                + "Bohr-Mollerup convexity, Binet's digamma formula and the integral test. "
                + "The zero expansion uses the classical entire-function logarithmic derivative "
                + "method and reflection symmetry. These are repository derivations from those "
                + "classical ingredients. For a general character q is the modulus; for a "
                + "primitive character it is also the conductor. The normalization differs "
                + "from the usual parity-dependent (q/pi) completion by the constant q to "
                + "the power minus a/2, where a is zero or one according to parity.")),
            Describe.Lean(DescribeId.Create("entire-completion"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.differentiable_completion"),
                H("Entire nonprincipal completions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q and nonprincipal complex Dirichlet character "
                    + "chi, Fchi(s) = exp((log(q)/2)s) completedLFunction(chi,s) is complex "
                    + "differentiable on the whole plane. Primitivity is unnecessary. The "
                    + "exponential factor is entire and never vanishes; Mathlib supplies the "
                    + "entire completed L-function."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-equation"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_one_sub"),
                H("The normalized functional equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every primitive complex character of positive modulus and every complex "
                    + "s, Fchi(1-s) = rootNumber(chi) FchiInverse(s). Nonprincipality is "
                    + "unnecessary. The factor q to the power s minus one half in the classical "
                    + "completed functional equation cancels against the exponential "
                    + "normalizations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_ne_zero_of_one_le_re"),
                H("The closed right half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q, every complex character chi and every s with "
                    + "Re(s) at least one, Fchi(s) is nonzero if chi is nonprincipal, s is not "
                    + "one, or q is one. Primitivity is unnecessary. The completion-to-L-function "
                    + "quotient and the classical nonvanishing theorem give this implication. For "
                    + "q = 1 at s = 1 the assertion uses the totalized value in Mathlib, and does "
                    + "not mean that the pole has a finite analytic value."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.rootNumber_ne_zero"),
                H("A nonzero root number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every primitive complex character of positive modulus, the root number "
                    + "is nonzero. Apply the normalized functional equation at minus one and use "
                    + "the nonzero completion value at two. No nonprincipal or prime-modulus "
                    + "assumption is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-nonvanishing"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_ne_zero_of_re_le_zero"),
                H("The closed left half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every primitive complex character of positive modulus, Fchi(s) is "
                    + "nonzero whenever Re(s) is at most zero. No nonprincipality hypothesis is "
                    + "needed: reflection reaches the closed right half-plane, and a primitive "
                    + "principal character has modulus one. At modulus one and s = 0 this is an "
                    + "assertion about the totalized value of the completed zeta function, not a "
                    + "finite analytic value at its pole."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjugate-completion"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_inv_conj"),
                H("Conjugation and inversion of a character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex character of positive modulus and every complex s, "
                    + "FchiInverse(conjugate(s)) = conjugate(Fchi(s)). Neither nonprincipality nor "
                    + "primitivity is required. The completed even and odd Hurwitz functions are "
                    + "Mellin transforms of real modified kernels with real correction terms. "
                    + "Conjugation commutes with these integrals and with powers of positive real "
                    + "numbers, so the equality includes totalized special values."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-root-number"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.norm_rootNumber"),
                H("Unit norm for every primitive root number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Every primitive complex character of positive modulus has root number of "
                    + "norm one. For a nonprincipal character, take norms in the functional "
                    + "equation at two and minus one, use conjugation to identify the "
                    + "inverse-character norms, and cancel a nonzero completion value. A primitive "
                    + "principal character has modulus one, for which the root number is one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-radius-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.right_growth_radius"),
                H("A free radius in the right half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Let q be positive and chi nonprincipal. If Re(s) is at least one half and "
                    + "norm(s) is at most the real radius R, then norm(Fchi(s)) is strictly below "
                    + "B phi(q) R exp((log(q)/2)R + U log(U)), where B = max(1,Gamma(1/4)) and U = "
                    + "(R+3)/2. Primitivity and a separate condition R at least one are "
                    + "unnecessary. The hypotheses already imply R at least one half."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("free-radius-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_growth_radius"),
                H("A radius that covers the reflected point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For positive q and nonprincipal chi, the same strict bound B phi(q) R "
                    + "exp((log(q)/2)R + U log(U)) holds at s provided norm(s) is at most R, "
                    + "either Re(s) is at least one half or chi is primitive, and whenever Re(s) "
                    + "is below one half the reflected point 1-s also has norm at most R. Here U = "
                    + "(R+3)/2. Primitivity is used only in the reflected branch, through the "
                    + "functional equation and unit root-number norm."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("explicit-global-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_growth_explicit"),
                H("A radial Gamma bound on the whole plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For positive q and primitive nonprincipal chi, set B = max(1,Gamma(1/4)), R "
                    + "= 1 + norm(s), and U = (R+3)/2. At every complex s, norm(Fchi(s)) is "
                    + "strictly below B phi(q) R exp((log(q)/2)R + U log(U)). This follows from "
                    + "the free-radius estimate, since R bounds both norm(s) and norm(1-s)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("logarithmic-global-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_growth_log"),
                H("An explicit logarithmic growth coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Set B = max(1,Gamma(1/4)) and C = max(log(B phi(q)) + log(q)/2 + 2 log(2), "
                    + "3). For positive q and primitive nonprincipal chi, with R = 1 + norm(s), "
                    + "norm(Fchi(s)) is strictly below exp(C R (1+log(R))). The comparison U at "
                    + "most 2R absorbs the radial Gamma argument. Since 1+log(R) is at most 3 "
                    + "sqrt(R) for R at least one, a bound exp(3 C R to the power 3/2) follows. It "
                    + "supplies the growth exponent below two for the two-point logarithmic "
                    + "derivative formula; exact order one is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-zero-order"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_zero_order"),
                H("Finite order and positive zero multiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q, nonprincipal chi and complex rho, the "
                    + "analytic order of Fchi at rho is finite, and Fchi(rho) = 0 if and only if "
                    + "its natural analytic order is positive. Primitivity is unnecessary. Entire "
                    + "continuation and the nonzero value at two exclude local identical vanishing "
                    + "by analytic continuation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("open-critical-strip"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_zero_strip"),
                H("The open critical strip contains every zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For primitive nonprincipal chi of positive modulus, every zero rho of Fchi "
                    + "satisfies 0 < Re(rho) < 1. The closed right half-plane is zero free; the "
                    + "functional equation and nonzero root number give the same conclusion on the "
                    + "closed left half-plane."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("critical-reflection"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_reflect"),
                H("Conjugate covariance across the critical line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every primitive complex character of positive modulus and every s, "
                    + "Fchi(1-conjugate(s)) = rootNumber(chi) conjugate(Fchi(s)). Nonprincipality "
                    + "is unnecessary. This is the functional equation combined with the "
                    + "conjugation identity for the inverse character."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reflection-multiplicity"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_reflect_order"),
                H("Reflection preserves analytic multiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For primitive nonprincipal chi, reflection rho to 1-conjugate(rho) "
                    + "preserves the zero set and the full extended-natural analytic order at "
                    + "every point. Conjugating both sides of the function conjugates every "
                    + "iterated derivative, while affine reflection has nonzero derivative and "
                    + "multiplication by the nonzero root number does not change analytic order."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("vertical-resolvent"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_vertical_resolvent"),
                H("The positive vertical resolvent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For primitive nonprincipal chi and every real t, the zero-indexed series "
                    + "with term m(rho)(2-Re(rho))/((2-Re(rho)) squared + (t-Im(rho)) squared) has "
                    + "sum Re(Hchi(2+it)), where m(rho) is the natural analytic order and Hchi is "
                    + "the logarithmic derivative of Fchi. Apply the entire two-point difference "
                    + "formula at 2+it and -1+it. Conjugate reflection makes the difference of "
                    + "logarithmic derivatives equal twice the real part. Taking real parts gives "
                    + "the sum of a positive kernel and its multiplicity-preserving reflected "
                    + "kernel. Reindex this summable real expression to obtain the formula without "
                    + "separating potentially nonsummable complex fractions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dirichlet-log-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.norm_logDeriv_LFunction_two"),
                H("A uniform bound for the Dirichlet logarithmic derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus, every complex character and every real t, the "
                    + "norm of the logarithmic derivative of Lchi at 2+it is at most A = log(2)/4 "
                    + "+ 4 log(3)/9 + 1/3, which is less than one. No primitivity or "
                    + "nonprincipality hypothesis is imposed. The von Mangoldt Dirichlet series "
                    + "and character norm bound reduce the estimate to the logarithmic series at "
                    + "exponent two. Its first terms and an integral tail give A."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("logarithmic-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_logDeriv"),
                H("The three logarithmic derivative factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive q, every complex character chi and every s with Re(s) > "
                    + "1, Hchi(s) = (log(q)-log(pi))/2 + psi((s+a)/2)/2 + hchi(s), where hchi is "
                    + "the logarithmic derivative of Lchi and a is zero for even chi and one "
                    + "otherwise. All factors are holomorphic and nonzero in this region. The "
                    + "product rule, the real Gamma-factor identity and its digamma logarithmic "
                    + "derivative yield the equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-center-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_center_bound"),
                H("A sharper estimate at the real center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q and every complex character chi, twice "
                    + "Re(Hchi(2)) is at most log(q)-log(pi)+log(3/2)+2A, where A is "
                    + "log(2)/4+4 log(3)/9+1/3. No primitivity or nonprincipality is required. "
                    + "At the real Gamma argument, which lies between one and three halves, "
                    + "the real digamma bound psi(x) at most log(x) gives the sharper "
                    + "archimedean contribution. Combining this with the Dirichlet bound "
                    + "gives the stated estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("explicit-vertical-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletion.completion_vertical_bound"),
                H("An explicit bound for every vertical height"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every positive modulus q, complex character chi and real t, "
                    + "Re(Hchi(2+it)) is strictly below "
                    + "(log(q)-log(pi)+log(abs(t)+3))/2+A, with "
                    + "A = log(2)/4+4 log(3)/9+1/3. If chi is primitive and nonprincipal, "
                    + "the same real part is nonnegative. The upper estimate requires "
                    + "neither assumption: separate the three logarithmic derivative "
                    + "factors, apply Binet's bound on the Gamma strip, and use the "
                    + "Dirichlet-series estimate A. The lower estimate follows from the "
                    + "nonnegative multiplicity-weighted vertical resolvent. Since A < 1 "
                    + "and log(pi) > 1, the upper estimate implies "
                    + "Re(Hchi(2+it)) <= log(q(abs(t)+3))/2+1/2. At t = 0 the sharper "
                    + "real-center estimate implies twice Re(Hchi(2)) <= log(q)+2."))),
                DescribeRole.Theorem))));
}
