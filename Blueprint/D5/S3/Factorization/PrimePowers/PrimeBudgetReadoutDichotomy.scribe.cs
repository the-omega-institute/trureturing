using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class PrimeBudgetReadoutDichotomyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime budgets separate horizontal CRT factors from vertical precision maps.",
        H("Prime Budget Readout Dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("horizontal-prime-decomposition"),
                DeclarationHandle.Create(Prefix + "horizontal_prime_decomposition"),
                H("Different primes decompose horizontally by CRT"),
                StatementSource.FromAuthor(HorizontalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A PrimeBudget consists of a finite support, an exponent map, a "
                            + "primality proof on the support, and positivity of every "
                            + "supported exponent.")),
                    Paragraph(Text(
                        "The proof applies finite_crt_join directly to the support and "
                            + "exponent fields. The product is a dependent product of residue "
                            + "rings; no tensor-product object is introduced.")),
                    Paragraph(Text(
                        "The empty and singleton supports are included. The imported CRT "
                            + "lemma permits zero exponents, while PrimeBudget intentionally "
                            + "excludes them to represent the source definition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("vertical-prime-inverse-system"),
                DeclarationHandle.Create(Prefix + "vertical_prime_inverse_system"),
                H("One prime carries compatible precision projections"),
                StatementSource.FromAuthor(VerticalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The named primePowerReadout casts one integer into ZMod of p to the "
                            + "k. When the lower exponent is at most the upper exponent, "
                            + "primePowerProjection is Mathlib's ZMod.castHom.")),
                    Paragraph(Text(
                        "ZMod.castHom_self and ZMod.castHom_comp prove the identity and "
                            + "composition laws. ZMod.cast_intCast proves that every integer "
                            + "readout commutes with reduction of precision.")),
                    Paragraph(Text(
                        "These laws are the requested inverse-system compatibility data. No "
                            + "inverse-limit object is required, and no primality premise is "
                            + "used in the vertical direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("horizontal-vertical-dichotomy"),
                DeclarationHandle.Create(Prefix + "horizontal_vertical_dichotomy"),
                H("Horizontal CRT and vertical filtration hold together"),
                StatementSource.FromAuthor(DichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive prime budget, the existing CRT decomposition holds "
                        + "and every supported prime has the compatible vertical system. "
                        + "This is the single bundled structure principle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("precision-order-is-necessary"),
                DeclarationHandle.Create(Prefix + "precision_order_is_necessary"),
                H("Precision order is necessary for natural projections"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is no unital ring homomorphism from ZMod 2 to ZMod 4: two is zero "
                        + "in the source but nonzero in the target. Thus a projection cannot "
                        + "in general run from lower precision to higher precision."))),
                DescribeRole.Lemma))));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ZModOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ZMod")), Open, modulus, Close);

    private static Formula NonemptyOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Nonempty")), Open, type, Close);

    private static Formula Predicate(Formula name, Formula argument) =>
        At(name, argument);

    private static Formula HorizontalFormula()
    {
        Formula budget = F.Id("B");
        return Disp(Seq(
            Forall, Sp, budget, Colon, Sp, F.Id("PrimeBudget"), Comma, Sp,
            Predicate(F.Id("HorizontalPrimeDecomposition"), budget), Dot));
    }

    private static Formula VerticalFormula()
    {
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Predicate(F.Id("VerticalPrimeInverseSystem"), prime), Dot));
    }

    private static Formula DichotomyFormula()
    {
        Formula budget = F.Id("B");
        Formula prime = F.Id("p");
        Formula support = new Formula.Subscript(F.Id("S"), budget);
        return Disp(Seq(
            Forall, Sp, budget, Colon, Sp, F.Id("PrimeBudget"), Comma, RowBreak, Grp(),
            Predicate(F.Id("HorizontalPrimeDecomposition"), budget), Sp, Land, Sp,
            Forall, Sp, prime, Sp, InMacro, Sp, support, Comma, Sp,
            Predicate(F.Id("VerticalPrimeInverseSystem"), prime), Dot));
    }

    private static Formula NecessityFormula()
    {
        Formula hom = new Formula.TypeArrow(ZModOf(D(2)), ZModOf(D(4)));
        return Disp(Seq(Neg, NonemptyOf(hom), Dot));
    }
}
