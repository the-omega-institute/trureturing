using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LowerHalfPlaneFactorContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient continuity of supplied monic lower half-plane polynomial factors, including repeated roots.",
        H("Lower Half-Plane Factor Continuity"),
        Blocks(Describe.Lean(
            DescribeId.Create("continuous-coeff-of-monic-lower-factor"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/LowerHalfPlaneFactorContinuity.continuous_coeff_of_monic_lower_factor"),
            H("Continuity without choosing continuous root labels"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be a first-countable topological space, let m be any natural "
                    + "number, and let H and B assign complex polynomials to points a of A. "
                    + "Assume B(a) is monic of natural degree exactly m, and every complex z "
                    + "with B(a)(z)=0 satisfies Im(z)<0. Write B(a)# for the polynomial obtained "
                    + "by conjugating every coefficient, so B(a)#(z)=conj(B(a)(conj(z))). "
                    + "Assume H(a)=B(a)B(a)# and every coefficient of H is a continuous function "
                    + "of a. Then, for every natural k, the coefficient [X^k]B(a) is continuous "
                    + "in a. A need not be Hausdorff or compact.")),
                Paragraph(Text("The assumptions imply that H(a) is monic of degree 2m, has real "
                    + "coefficients, and has no real roots. Thus the theorem applies in "
                    + "particular when these properties of H are supplied explicitly. "
                    + "For m=0, monicity forces B(a)=1 and consequently H(a)=1. No positivity "
                    + "assumption on m, simple-root assumption, root-separation bound, or "
                    + "global bound on the roots is imposed.")),
                Paragraph(Text("For a convergent parameter sequence, the sum of the norms of "
                    + "the nonleading coefficients of H is bounded. The coefficient-sum "
                    + "Cauchy estimate bounds every root of B by one fixed radius. Enumerate "
                    + "the roots of each B with multiplicity using a finite index set; these "
                    + "enumerations need not vary continuously. Compactness of the product "
                    + "of the closed root disks gives a convergent subsequence of tuples. "
                    + "The corresponding monic products converge coefficientwise.")),
                Paragraph(Text("The exact identity H=B B# passes to this limit. Every limiting "
                    + "root has nonpositive imaginary part and is a root of the limiting H. "
                    + "The supplied lower factor at the limit excludes real roots, so all "
                    + "limiting roots remain strictly lower. A lower polynomial is coprime "
                    + "to the conjugate of another lower polynomial. Divisibility in the "
                    + "exact product identity, equal degrees and monicity therefore identify "
                    + "the limiting factor with B at the limiting parameter. This preserves "
                    + "full multiplicities. Applying this reasoning to every subsequence "
                    + "proves sequential continuity, hence continuity on A.")),
                Paragraph(Text("For a continuous real coefficient family s, the intended "
                    + "application sets H(s)=C(1/lambda(s)) times the complexification of "
                    + "d+s^2, where lambda(s)=delta+([X^m]s)^2 and delta>0. Once a monic "
                    + "lower factor B of this normalized polynomial is supplied, the theorem "
                    + "gives coefficient continuity of B. Multiplication by sqrt(lambda(s)) "
                    + "recovers the positive-leading factor b. Its nonzero value at -1 "
                    + "allows the phase normalization b times conj(b(-1))/|b(-1)|. The "
                    + "positive-leading normalization and the positive-anchor normalization "
                    + "are distinct.")),
                Paragraph(Text("This is a synthesis of classical polynomial factorization, "
                    + "Cauchy root bounds, compactness and coprimality. The existing root-bound "
                    + "theorem in CompactSeparatedRealContinuation and Mathlib's algebraic "
                    + "factorization and sequential compactness results are reused. No claim "
                    + "of literature originality is made. The theorem assumes the factors; "
                    + "it does not construct them, count the lower roots of an arbitrary "
                    + "real polynomial, construct the anchored evaluation homeomorphism, "
                    + "or establish the full telescoping-square or detector construction. "
                    + "It makes no physical-realization or algorithmic-complexity claim."))),
            DescribeRole.Theorem))));
}
