/* GID: D5/S3/Constants/Irrationality/LogNaturalIrrationality
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/LogNaturalIrrationality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The natural logarithm of every natural number at least two is irrational. */

using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class LogNaturalIrrationalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The natural logarithm of every natural number at least two is irrational.",
        H("Irrationality of Natural Logarithms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("natural-logarithms-of-naturals-are-irrational"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Irrationality/LogNaturalIrrationality."
                    + "irrational_log_natCast"),
                H("Every natural argument at least two has irrational logarithm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Le, Sp, F.Id("n"), Sp, Implies, Sp,
                    Call("Irrational", Call("log", F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "First fix a positive natural number a and suppose exp(a) = u/v "
                        + "with integer numerator u and positive natural denominator v. "
                        + "Positivity of the exponential gives u > 0. Apply Mathlib's "
                        + "LindemannWeierstrass.exp_polynomial_approx to the integer "
                        + "polynomial X - a. For every prime p > a this gives an integer z "
                        + "not divisible by p and an integer-coefficient polynomial g, "
                        + "with |z exp(a) - p g(a)| at most c^p/(p-1)! for one fixed real c. "
                        + "Polynomial evaluation at the integer a is an integer.")),
                    Paragraph(Text(
                        "Multiplication by v bounds the absolute value of the integer "
                        + "k = z u - p g(a) v by v c^p/(p-1)!. Mathlib's factorial "
                        + "decay theorem makes this upper bound tend to zero, including "
                        + "when c is negative. Infinitude of primes permits p to exceed "
                        + "a, |u|, and the threshold where the bound is less than one. "
                        + "Thus k = 0 and p divides z u. Primality forces p to divide "
                        + "z or u. The first possibility contradicts the approximation "
                        + "supplier, and the second contradicts 0 < |u| < p. Hence the "
                        + "exponential of each positive natural number is irrational.")),
                    Paragraph(Text(
                        "Now let n be any natural number at least two. If log(n) were "
                        + "rational, write it in normalized form A/B with positive natural "
                        + "denominator B. Since log(n) > 0, its integer numerator A is "
                        + "positive. The identity B log(n) = A gives exp(A) = n^B. "
                        + "The right side is an integer, contradicting the exponential "
                        + "irrationality just established. This proves the entire infinite "
                        + "family, without a bound on n.")),
                    Paragraph(Text(
                        "The analytical approximation is attributed to Mathlib's "
                        + "Lindemann analytical part, authored by Yuyang Zhao, whose "
                        + "source cites Jacobson's Basic Algebra I. The argument uses "
                        + "that approximation and elementary prime divisibility; it "
                        + "does not invoke the full Lindemann-Weierstrass transcendence "
                        + "or linear-independence theorem. The result supplies constant "
                        + "irrationality for arithmetic rotations and makes no return "
                        + "threshold, distribution, or new literature-novelty assertion."))),
                DescribeRole.Theorem))));
}
