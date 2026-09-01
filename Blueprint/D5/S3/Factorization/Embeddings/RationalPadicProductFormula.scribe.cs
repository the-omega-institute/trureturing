using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class RationalPadicProductFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Embeddings/RationalPadicProductFormula.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The usual rational norm and all prime-indexed p-adic norms satisfy the product formula.",
        H("The Rational p-adic Product Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-padic-norm-finite-support"),
                DeclarationHandle.Create(Prefix + "rational_padic_norm_hasFiniteMulSupport"),
                H("Only finitely many p-adic factors are nontrivial"),
                StatementSource.FromAuthor(FiniteSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero rational, every prime outside the numerator and denominator "
                        + "factorization supports has p-adic norm one. Thus the all-primes "
                        + "product is algebraically finite and needs no convergence premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-padic-product-formula"),
                DeclarationHandle.Create(Prefix + "rational_padic_product_formula"),
                H("The rational archimedean and p-adic norms multiply to one"),
                StatementSource.FromAuthor(ProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write a nonzero rational as its reduced integer numerator divided by "
                            + "its positive natural denominator. Prime factorization shows that "
                            + "the finite product of p-adic norms of each nonzero natural number "
                            + "is its reciprocal.")),
                    Paragraph(Text(
                        "The p-adic norm ignores the sign of the numerator and respects division. "
                            + "The numerator and denominator factors therefore cancel the usual "
                            + "absolute value exactly, leaving one."))),
                DescribeRole.Theorem))));

    private static Formula FiniteSupportFormula()
    {
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula support = Seq(
            OpenBrace, p, Sp, InMacro, Sp, PrimeType(), Sp, Mid, Sp,
            PadicNorm(x, p), Sp, Neq, Sp, D(1), CloseBrace);
        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("Finite")), Open, support, Close, Dot));
    }

    private static Formula ProductFormula()
    {
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula finiteProduct = Seq(
            Prod, Caret, Grp(Operatorname, Grp(F.Id("fin"))),
            Underscore, Grp(p, Sp, InMacro, Sp, PrimeType()), Sp,
            PadicNorm(x, p));
        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            ArchimedeanNorm(x), Sp, finiteProduct, Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula PadicNorm(Formula value, Formula prime) =>
        Seq(new Formula.Absolute(value), Underscore, prime);

    private static Formula ArchimedeanNorm(Formula value) =>
        Seq(new Formula.Absolute(value), Underscore, Infty);

    private static Formula PrimeType() =>
        Seq(F.Id("Nat"), Dot, F.Id("Primes"));

    private static Formula RationalNumbers() =>
        Seq(Mathbb, Grp(F.Id("Q")));
}
