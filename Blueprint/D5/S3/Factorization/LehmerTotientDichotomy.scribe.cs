using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class LehmerTotientDichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/LehmerTotientDichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lehmer's totient divisibility condition yields a prime/composite structural dichotomy.",
        H("Lehmer Totient Divisibility Dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("korselt-condition"),
                DeclarationHandle.Create(Prefix + "IsKorselt"),
                H("Korselt's local divisibility condition"),
                StatementSource.FromAuthor(IsKorseltFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsKorselt records squarefreeness together with divisibility of n - 1 "
                        + "by p - 1 for every prime divisor p of n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-divides-totient-from-square-divisor"),
                DeclarationHandle.Create(Prefix + "prime_dvd_totient_of_sq_dvd"),
                H("A repeated prime factor enters the totient"),
                StatementSource.FromAuthor(PrimeDividesTotientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The totient of p squared is p times p - 1. Totient divisibility under "
                        + "divisibility then transports the factor p from p squared to n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("squarefree-from-totient-divisibility"),
                DeclarationHandle.Create(Prefix + "squarefree_of_totient_dvd_pred"),
                H("Lehmer divisibility forces squarefreeness"),
                StatementSource.FromAuthor(SquarefreeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If p squared divided n, then p would divide both n and n - 1 through "
                        + "the totient hypothesis. This would force p to divide one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("squarefree-totient-product"),
                DeclarationHandle.Create(
                    Prefix + "totient_eq_prod_primeFactors_sub_one_of_squarefree"),
                H("The squarefree totient is a prime-factor product"),
                StatementSource.FromAuthor(TotientProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero squarefree n, the product of the distinct prime factors is "
                        + "n, so Mathlib's totient product formula reduces to the product of p - 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("composite-branch-is-odd"),
                DeclarationHandle.Create(Prefix + "odd_of_totient_dvd_pred_of_not_prime"),
                H("The composite branch is odd"),
                StatementSource.FromAuthor(OddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A composite n greater than one has even totient. If n were even as well, "
                        + "two would divide both n and n - 1, hence one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-product-divides-predecessor"),
                DeclarationHandle.Create(Prefix + "prod_primeFactors_sub_one_dvd_pred"),
                H("The prime-factor product divides the predecessor"),
                StatementSource.FromAuthor(ProductDividesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Squarefreeness identifies the displayed product with the totient, so the "
                        + "assumed divisibility transfers to the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("korselt-condition-from-totient-divisibility"),
                DeclarationHandle.Create(Prefix + "isKorselt_of_totient_dvd_pred"),
                H("Lehmer divisibility implies the Korselt condition"),
                StatementSource.FromAuthor(KorseltBridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each p - 1 is a factor of the squarefree totient product, which divides "
                        + "n - 1; the preceding theorem supplies squarefreeness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-power-divides-predecessor"),
                DeclarationHandle.Create(Prefix + "two_pow_card_primeFactors_dvd_pred"),
                H("The prime-factor count supplies a power of two"),
                StatementSource.FromAuthor(TwoPowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime factor on the odd composite branch is odd, so each p - 1 "
                        + "contributes a factor of two to the totient product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("at-least-three-prime-factors"),
                DeclarationHandle.Create(Prefix + "three_le_card_primeFactors"),
                H("The composite branch has at least three prime factors"),
                StatementSource.FromAuthor(ThreeFactorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Squarefreeness excludes a prime power. The remaining two-factor case "
                        + "would make (p - 1)(q - 1) divide pq - 1, but a direct estimate "
                        + "forces the quotient to be one and yields a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("totient-divisibility-dichotomy"),
                DeclarationHandle.Create(Prefix + "totient_dvd_pred_dichotomy"),
                H("Prime or full composite structural package"),
                StatementSource.FromAuthor(DichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A number satisfying the totient divisibility condition is prime, or it is "
                        + "odd, squarefree, Korselt, satisfies the product divisibility, carries "
                        + "the full two-adic factor, and has at least three distinct prime factors."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N => F.Id("n");
    private static Formula P => F.Id("p");
    private static Formula Pred(Formula value) => Seq(value, Sp, Minus, Sp, D(1));
    private static Formula PrimeFactors(Formula value) => Call("primeFactors", value);
    private static Formula Totient(Formula value) => Call("totient", value);
    private static Formula Divides(Formula left, Formula right) =>
        Seq(left, Sp, Mid, Sp, right);

    private static Formula Product(Formula value) => Seq(
        Prod, Underscore, Grp(P, Sp, InMacro, Sp, PrimeFactors(value)), Sp,
        Grp(Pred(P)));

    private static Formula LehmerHypotheses(Formula value) => Seq(
        D(1), Sp, Lt, Sp, value, Sp, Land, Sp,
        Divides(Totient(value), Pred(value)));

    private static Formula CompositeHypotheses(Formula value) => Seq(
        LehmerHypotheses(value), Sp, Land, Sp,
        Neg, Sp, Call("Prime", value));

    private static Formula IsKorseltFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        Call("IsKorselt", N), Sp, Colon, Eq, Sp,
        Call("Squarefree", N), Sp, Land, Sp,
        Forall, Sp, P, Sp, InMacro, Sp, PrimeFactors(N), Comma, Sp,
        Divides(Pred(P), Pred(N)), Dot));

    private static Formula PrimeDividesTotientFormula() => Disp(Seq(
        Forall, Sp, P, Comma, Sp, N, Sp, InMacro, Sp, NatType, Comma, RowBreak, Grp(),
        Call("Prime", P), Sp, Land, Sp,
        Divides(Seq(Grp(P), Caret, Grp(D(2))), N), Sp,
        Rightarrow, Sp, Divides(P, Totient(N)), Dot));

    private static Formula SquarefreeFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, Sp,
        LehmerHypotheses(N), Sp, Rightarrow, Sp, Call("Squarefree", N), Dot));

    private static Formula TotientProductFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        N, Sp, Neq, Sp, D(0), Sp, Land, Sp, Call("Squarefree", N), Sp,
        Rightarrow, Sp, Totient(N), Sp, Eq, Sp, Product(N), Dot));

    private static Formula OddFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        CompositeHypotheses(N), Sp, Rightarrow, Sp, Call("Odd", N), Dot));

    private static Formula ProductDividesFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        LehmerHypotheses(N), Sp, Rightarrow, Sp,
        Divides(Product(N), Pred(N)), Dot));

    private static Formula KorseltBridgeFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        LehmerHypotheses(N), Sp, Rightarrow, Sp, Call("IsKorselt", N), Dot));

    private static Formula TwoPowerFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        CompositeHypotheses(N), Sp, Rightarrow, Sp,
        Divides(
            Seq(D(2), Caret, Grp(Call("card", PrimeFactors(N)))),
            Pred(N)), Dot));

    private static Formula ThreeFactorsFormula() => Disp(Seq(
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        CompositeHypotheses(N), Sp, Rightarrow, Sp,
        D(3), Sp, Le, Sp, Call("card", PrimeFactors(N)), Dot));

    private static Formula CompositePackage(Formula value) => Seq(
        Call("Odd", value), Sp, Land, Sp,
        Call("Squarefree", value), Sp, Land, Sp,
        Call("IsKorselt", value), Sp, Land, RowBreak, Grp(),
        Divides(Product(value), Pred(value)), Sp, Land, RowBreak, Grp(),
        Divides(
            Seq(D(2), Caret, Grp(Call("card", PrimeFactors(value)))),
            Pred(value)), Sp, Land, RowBreak, Grp(),
        D(3), Sp, Le, Sp, Call("card", PrimeFactors(value)));

    private static Formula DichotomyFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, Typed(N, NatType), Comma, RowBreak, Grp(),
        LehmerHypotheses(N), Sp, Rightarrow, RowBreak, Grp(),
        Call("Prime", N), Sp, Lor, Sp, Grp(CompositePackage(N)), Dot,
        End, Grp(F.Id("gathered"))));
}
