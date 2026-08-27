using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class MonsterPrimitiveMobiusRecoveryDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mobius inversion recovers primitive coefficients from logarithmic histories.",
        H("Monster Primitive Mobius Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monster-primitive-mobius-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery."
                        + "monster_primitive_mobius_recovery"),
                H("Logarithmic histories determine every primitive coefficient"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I index the primitive root rays. The functions H and L record the "
                            + "rational coefficients at positive multiples of every ray in the "
                            + "primitive heat series and the negative logarithmic denominator.")),
                    Paragraph(Text(
                        "The hypothesis is the coefficient form of the logarithmic expansion: "
                            + "multiplying degree n by the source factor 1/k turns it into the "
                            + "displayed divisor sum.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies divisor-sum Mobius inversion. Applying it to "
                            + "the degree-scaled coefficients and cancelling positive n gives "
                            + "exactly the factor mu(k)/k in the recovery formula."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula rationals = F.Seq(F.Mathbb, F.Grp(F.Id("Q")));
        Formula indexType = F.Id("I");
        Formula coefficientFamily = new Formula.TypeArrow(
            indexType,
            new Formula.TypeArrow(naturals, rationals));
        Formula h = F.Id("H"), l = F.Id("L");
        Formula ray = F.Id("ray");
        Formula n = F.Id("n"), d = F.Id("d"), k = F.Id("k"), r = F.Id("r");

        Formula At(Formula family, Formula first, Formula second) =>
            new Formula.Apply(family, [first, second]);
        Formula Equal(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula Multiply(Formula left, Formula right) =>
            new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula.BoundVariable Bound(string name, Formula domain) =>
            new(FormulaIdentifier.Create(name), domain);

        Formula positive = new Formula.Relation(
            n,
            FormulaRelationOperator.GreaterThan,
            D(0));
        Formula expansionSum = F.Seq(
            F.Sum, F.Underscore, F.Grp(d, F.Sp, F.Mid, F.Sp, n), F.Sp,
            Multiply(d, At(h, ray, d)));
        Formula scaledExpansion = Equal(
            expansionSum,
            Multiply(n, At(l, ray, n)));
        Formula expansion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("ray", indexType), Bound("n", naturals)],
            Implies(positive, scaledExpansion));

        Formula factorPair = F.Grp(
            Multiply(k, r), F.Sp, F.Eq, F.Sp, n);
        Formula mobiusWeight = new Formula.Fraction(
            F.Seq(F.Mu, F.Open, k, F.Close),
            k);
        Formula recoverySum = F.Seq(
            F.Sum, F.Underscore, factorPair, F.Sp,
            Multiply(mobiusWeight, At(l, ray, r)));
        Formula recovered = Equal(At(h, ray, n), recoverySum);
        Formula recovery = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("ray", indexType), Bound("n", naturals)],
            Implies(positive, recovered));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", F.Id("Type")),
                Bound("H", coefficientFamily),
                Bound("L", coefficientFamily),
            ],
            Implies(expansion, recovery)));
    }
}
