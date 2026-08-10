using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class AlmostAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Deficit/AlmostAdditivity",
            "The contraction reading is almost additive over prime exponents."),
        H("Almost Additivity of the Contraction Reading"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-contraction-reading-is-almost-additive"),
                H("The contraction reading is almost additive"),
                LeanTheorem(
                    "D5/S1/Deficit/AlmostAdditivity.lambdaMinus_almost_additive"),
                Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, F.Id("n"), Ge, D(1), Comma, Quad,
                    Lvert,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("mn"), Close, Minus,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("m"), Close, Minus,
                    Operatorname, Grp(F.Id("lambdaMinus")), Open,
                    F.Id("n"), Close,
                    Rvert, Leq, Log, Open,
                    Operatorname, Grp(F.Id("rad")), Open,
                    Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close,
                    Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For positive natural numbers m and n, the contraction reading of their "
                        + "product differs from the sum of their separate readings by at most the "
                        + "natural logarithm of the product of the distinct primes common to m and "
                        + "n. The module defines that distinct-prime product explicitly and defines "
                        + "the reading as a finite sum over prime exponents, so the displayed bound "
                        + "formalizes the source atom without hiding either arithmetic object behind "
                        + "an assumption.")),
                    Paragraph(Text(
                        "The proof expands the factorization of mn and isolates the intersection of "
                        + "the two prime supports. Outside that intersection one exponent is zero, "
                        + "so the local defect vanishes. On a common prime axis the existing "
                        + "three-valued deficit theorem says that the defect has absolute value at "
                        + "most one. The triangle inequality then bounds the weighted sum by the sum "
                        + "of logarithms of the common primes, and the logarithm-of-a-finite-product "
                        + "identity turns that sum into the stated radical bound.")),
                    Paragraph(Text(
                        "This is not a thin wrapper around an exact library theorem. Mathlib supplies "
                        + "the prime-factorization multiplication law, the GCD support identity, the "
                        + "finite-sum triangle inequality, and the logarithm-of-product lemma; the "
                        + "repository's contraction-face deficit result provides the decisive local "
                        + "bound. Searches found no library declaration for the assembled "
                        + "almost-additivity statement.")))
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Deficit/DeficitThreeValued")),
        ]));
}
