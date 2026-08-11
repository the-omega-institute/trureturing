using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class LambdaMinusAdditiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Deficit/LambdaMinusAdditive",
            "The contraction reading is additive over coprime factors."),
        H("Additivity of the Contraction Reading over Coprimes"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-contraction-reading-is-additive-over-coprimes"),
                H("The contraction reading is additive over coprime factors"),
                LeanTheorem(
                    "D5/S1/Deficit/LambdaMinusAdditive.lambdaMinus_coprime_add"),
                Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, F.Id("n"), Comma, Quad,
                    Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close, Eq, D(1),
                    Sp, Implies, Sp,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("mn"), Close, Eq,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("m"), Close, Plus,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("n"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For coprime natural numbers m and n, the contraction reading of "
                        + "their product equals the sum of their separate readings exactly, with no "
                        + "error term. The reading is defined as a finite sum over prime exponents, "
                        + "and coprimality means m and n share no prime, so the two prime supports "
                        + "are disjoint and the sum over the product splits cleanly into the two "
                        + "separate sums.")),
                    Paragraph(Text(
                        "The proof rewrites the factorization of the product as the sum of the two "
                        + "factorizations and observes that the prime supports are disjoint, because "
                        + "coprime numbers have disjoint prime factors. A finitely-supported sum over "
                        + "a disjoint union of supports distributes as the sum of the two restricted "
                        + "sums, which are exactly the readings of m and of n.")),
                    Paragraph(Text(
                        "This is the exact companion of the almost-additivity bound: that result "
                        + "controls the failure of additivity by the logarithm of the product of the "
                        + "common primes, and here, when there are no common primes, that bound is "
                        + "zero and additivity holds on the nose. Mathlib supplies the "
                        + "prime-factorization multiplication law, the coprime disjoint-prime-factors "
                        + "identity, and the disjoint-support sum-splitting lemma; the repository "
                        + "supplies the contraction reading. Searches found no library declaration for "
                        + "the assembled coprime-additivity statement.")))
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Deficit/AlmostAdditivity")),
        ]));
}
