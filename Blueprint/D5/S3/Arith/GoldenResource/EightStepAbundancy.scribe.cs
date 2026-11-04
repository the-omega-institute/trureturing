using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class EightStepAbundancyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/EightStepAbundancy.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/Arith/wu2019abundant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unique largest abundancy at eight prime factors counted with multiplicity "
            + "is attained by 180180 and equals 224/55.",
        H("Eight-Step Abundancy Maximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-layer-denominator"),
                DeclarationHandle.Create(Prefix + "layerDenominator"),
                H("Prime-layer denominator"),
                StatementSource.FromAuthor(DenominatorFormula()),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(Paragraph(Text(
                    "D(p,k) denotes layerDenominator p k. It sums p to the powers one "
                        + "through k, with an empty sum at k = 0. For a prime p and a "
                        + "positive layer k, the multiplicative abundancy gain is 1 + 1/D(p,k)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("denominator-mono"),
                DeclarationHandle.Create(Prefix + "denominator_mono"),
                H("Monotonicity in the layer depth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(Paragraph(Text("For every natural p and depths a<=b, B(p,a)<=B(p,b). This is finite-sum monotonicity on nested ranges and supplies the denominator comparison in an actual prime-layer exchange."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("denominator-pos"),
                DeclarationHandle.Create(Prefix + "denominator_pos"),
                H("Positive prime-layer denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(Paragraph(Text("For every prime p and positive depth k, B(p,k)>0. The first layer equals p and every later layer adds a nonnegative natural power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("layer-ratio-identity"),
                DeclarationHandle.Create(Prefix + "layer_ratio_identity"),
                H("The exact multiplicative gain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(Paragraph(Text("For every prime p and positive depth k, (1-p^(-(k+1)))/(1-p^(-k))=1+1/B(p,k), interpreted in the reals. The finite geometric sum gives this identity and hence the exact gain used in actual one-layer abundancy comparisons."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-step-layer-cutoff"),
                DeclarationHandle.Create(Prefix + "eight_step_layer_cutoff"),
                H("The strict eighth-layer boundary"),
                StatementSource.FromAuthor(CutoffFormula()),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(
                    Paragraph(Text(
                        "The eight events, in denominator order, are (2,1), (3,1), (5,1), "
                            + "(2,2), (7,1), (11,1), (3,2), and (13,1). Their denominators "
                            + "are 2, 3, 5, 6, 7, 11, 12, and 13.")),
                    Paragraph(Text(
                        "The equivalence quantifies over every prime and every positive "
                            + "layer. Every excluded event has denominator at least 14. "
                            + "The proof first excludes all depths at least three by comparison "
                            + "with 2 + 4 + 8, then classifies the remaining prime bases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-step-abundancy-optimum"),
                DeclarationHandle.Create(Prefix + "eight_step_abundancy_optimum"),
                H("The unique eight-step maximizer"),
                StatementSource.FromAuthor(OptimumFormula()),
                AssessedProvenance.FromLiterature(Wu),
                Blocks(
                    Paragraph(Text(
                        "Here omega(n) is the sum of n's prime exponents, equivalently "
                            + "Mathlib's cardFactors n, and Z(n) is sigma(1,n)/n as a real number. "
                            + "The competitor ranges over every positive natural number with "
                            + "omega(n) = 8, without a bound on n or its prime factors.")),
                    Paragraph(Text(
                        "The proof applies the existing local threshold theorem at the two "
                            + "prices log(15/14) and log(14/13). Equality at their midpoint "
                            + "forces equality of each exponent. The existing objective "
                            + "factorization then sums the local comparisons over the union "
                            + "of the two finite prime supports; the equal eight-step costs cancel.")),
                    Paragraph(Text(
                        "The theorem includes the exact values, both eight-step counts, "
                            + "and 180180 = 2^2 * 3^2 * 5 * 7 * 11 * 13. The comparison "
                            + "with 5040 concerns abundancy at fixed step count. It does not "
                            + "assert a comparison for an objective penalizing integer size."))),
                DescribeRole.Theorem))));

    private static Formula DenominatorFormula() => Disp(ForAll(
        [Bound("p"), Bound("k")],
        Equal(Call("D", F.Id("p"), F.Id("k")),
            Seq(Sum, Underscore, Grp(Seq(F.Id("i"), Sp, InMacro, Sp,
                Call("range", F.Id("k")))), Sp,
                new Formula.Power(F.Id("p"), Add(F.Id("i"), D(1)))))));

    private static Formula CutoffFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula first = And(Equal(k, D(1)), Any(
            Equal(p, D(2)), Equal(p, D(3)), Equal(p, D(5)), Equal(p, D(7)),
            Equal(p, D(1, 1)), Equal(p, D(1, 3))));
        Formula second = And(Equal(k, D(2)), Any(Equal(p, D(2)), Equal(p, D(3))));
        return Disp(ForAll([Bound("p"), Bound("k")],
            Implies(And(Call("Prime", p), Le(D(1), k)),
                Iff(Lt(Call("D", p, k), D(1, 4)), Any(first, second)))));
    }

    private static Formula OptimumFormula()
    {
        Formula n = F.Id("n");
        Formula target = D(1, 8, 0, 1, 8, 0);
        Formula smaller = D(5, 0, 4, 0);
        Formula value = new Formula.Fraction(D(2, 2, 4), D(5, 5));
        Formula comparison = new Formula.Fraction(D(4, 0, 3), D(1, 0, 5));
        return Disp(new Formula.Aligned([
            Equal(Call("Z", target), value),
            ForAll([Bound("n")], Implies(
                And(Lt(D(0), n), Equal(Call("omega", n), D(8))),
                And(Le(Call("Z", n), value),
                    Iff(Equal(Call("Z", n), value), Equal(n, target))))),
            And(Equal(Call("Z", smaller), comparison),
                Lt(Call("Z", smaller), Call("Z", target))),
            And(Equal(Call("omega", target), D(8)),
                Equal(Call("omega", smaller), D(8))),
            Equal(target, Product(Product(Product(Product(Product(
                new Formula.Power(D(2), D(2)), new Formula.Power(D(3), D(2))),
                D(5)), D(7)), D(1, 1)), D(1, 3)))
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))));
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Product(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Any(params Formula[] alternatives) => alternatives.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.Or, b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
