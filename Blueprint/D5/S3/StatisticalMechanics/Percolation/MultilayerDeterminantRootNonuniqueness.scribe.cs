using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class MultilayerDeterminantRootNonuniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/guha2016multilayerpercolation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three layers with degree identically 65 give three distinct interior zeros of the multilayer percolation determinant, refuting its conjectured uniqueness.",
        H("Nonuniqueness of the multilayer percolation determinant zero"),
        Blocks(
            Node("matrix", "The multilayer matrix", MatrixFormula(),
                "Equation (3) of Guha, Towsley, Nain, Capar, Swami and Basu defines the matrix for "
                    + "M layers, excess-degree ratio C and occupation probability q. Here i and j range over "
                    + "Fin M, whose values are 0 through M − 1; the source indices are val(i) + 1 and "
                    + "val(j) + 1. The function choose is the natural binomial coefficient, zero when its "
                    + "lower argument exceeds its upper argument. Subtraction inside choose and in the "
                    + "exponents is natural subtraction; the binomial coefficients are cast to real numbers "
                    + "before their difference is taken. The definition allows every natural M and real C, q.",
                "multilayerMatrix"),
            Node("distribution", "Finitely supported degree distributions", DistributionFormula(),
                "The degree probabilities p(k) are nonnegative and sum to one. Finsupp(N,R) denotes "
                    + "the finitely supported real functions on the nonnegative integers; support(p) is the "
                    + "finite set where p is nonzero. Every displayed sum over support(p) is a finite sum. "
                    + "This is the finitely supported case of the source's degree distribution p_k.",
                "IsDegreeDistribution"),
            Node("mean", "The mean degree", MeanFormula(),
                "The source's mean degree is z = sum_k k p_k. The map castReal sends a natural number "
                    + "to the corresponding real number. The definition applies to every finitely supported "
                    + "real function p; positivity is imposed in the conjecture.",
                "meanDegree"),
            Node("excess", "The excess-degree ratio", ExcessFormula(),
                "The source sets C = sum_k (k − 1) k p_k / z. In this formula k is cast to R before "
                    + "subtracting one. The quotient uses real division, including its value at a zero "
                    + "denominator; the conjecture assumes that the mean degree is positive.",
                "excessRatio"),
            Node("claim", "The determinant uniqueness conjecture", ClaimFormula(),
                "For every M at least one and every finitely supported degree distribution with positive "
                    + "mean and excess-degree ratio greater than one, the determinant is asserted to have "
                    + "exactly one zero in the closed interval [0,1]. This is the finitely supported form "
                    + "of the conjecture following equation (5), repeated after Appendix C. A counterexample "
                    + "in this class also contradicts the assertion for arbitrary degree distributions.",
                "claim"),
            Describe.Lean(
                DescribeId.Create("multilayer-root-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Three distinct zeros for three layers"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take M = 3 and the point mass at degree 65: p(65) = 1 and p(k) = 0 for "
                            + "k different from 65. It is a finitely supported degree distribution with "
                            + "z = 65 and C = 64. With u = q(1 − q)^2, v = q^2(1 − q) and w = q^3, "
                            + "the matrix is [[1 − 64u, −128v, −64w], [−128u, 1 − 192v, −64w], "
                            + "[−192u, −192v, 1 − 64w]].")),
                    Paragraph(Text(
                        "Its determinant has the exact values 1, −36, 281 and −63 at q = 0, 1/4, "
                            + "1/2 and 1, respectively. Each entry is a polynomial in q, so the determinant "
                            + "is continuous. The intermediate value theorem gives a zero in each of "
                            + "(0,1/4), (1/4,1/2) and (1/2,1). The endpoint values are nonzero, so these "
                            + "zeros lie in the open intervals and are distinct. Thus uniqueness in [0,1] "
                            + "fails even though z > 0 and C > 1.")),
                    Paragraph(Text(
                        "This construction uses the source's matrix and degree data. It refutes the "
                            + "uniqueness conjecture; the source's separate proposition identifying the "
                            + "percolation threshold with the smallest zero is a different statement."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration) => Describe.Lean(
            DescribeId.Create("multilayer-root-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Distributions() => Call("Finsupp", Naturals(), Reals());
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffOf(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(Parenthesized(basis), Parenthesized(exponent));
    private static Formula SumOverSupport(Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(Typed(F.Id("k"), Naturals()), Sp, InMacro, Sp,
            Call("support", F.Id("p")))), Sp, Parenthesized(body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
        Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no));

    private static Formula MatrixFormula()
    {
        Formula m = F.Id("M"), c = F.Id("C"), q = F.Id("q"), i = F.Id("i"), j = F.Id("j");
        Formula column = Parenthesized(Add(Call("val", j), D(1)));
        Formula row = Parenthesized(Add(Call("val", i), D(1)));
        Formula common = Call("castReal", Call("choose", m, column));
        Formula diagonalDifference = Parenthesized(Sub(common,
            Call("castReal", Call("choose", Parenthesized(Sub(m, column)), column))));
        Formula offDiagonalDifference = Parenthesized(Sub(common,
            Call("castReal", Call("choose", Parenthesized(Sub(m, row)), column))));
        Formula occupation = Power(q, column);
        Formula vacancy = Power(Sub(D(1), q), Sub(m, column));
        Formula diagonal = Sub(D(1), Mul(Mul(Mul(c, diagonalDifference), occupation), vacancy));
        Formula offDiagonal = Mul(Mul(Mul(new Formula.Negate(c), offDiagonalDifference), occupation), vacancy);
        return All("M", Naturals(), All("C", Reals(), All("q", Reals(),
            All("i", Call("Fin", m), All("j", Call("Fin", m),
                Equal(Call("multilayerMatrix", m, c, q, i, j),
                    Conditional(Equal(i, j), diagonal, offDiagonal)))))));
    }

    private static Formula DistributionFormula()
    {
        Formula p = F.Id("p"), k = F.Id("k");
        return All("p", Distributions(), IffOf(Call("IsDegreeDistribution", p),
            And(All("k", Naturals(), AtMost(D(0), At(p, k))), Equal(SumOverSupport(At(p, k)), D(1)))));
    }

    private static Formula MeanFormula() => All("p", Distributions(),
        Equal(Call("meanDegree", F.Id("p")),
            SumOverSupport(Mul(Call("castReal", F.Id("k")), At(F.Id("p"), F.Id("k"))))));

    private static Formula ExcessFormula()
    {
        Formula k = Call("castReal", F.Id("k")), p = F.Id("p");
        Formula numerator = SumOverSupport(Mul(Mul(Parenthesized(Sub(k, D(1))), k), At(p, F.Id("k"))));
        return All("p", Distributions(), Equal(Call("excessRatio", p),
            new Formula.Fraction(numerator, Call("meanDegree", p))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        Formula interval = And(AtMost(D(0), q), AtMost(q, D(1)));
        Formula zero = Equal(Call("det", Parenthesized(
            Call("multilayerMatrix", F.Id("M"), Call("excessRatio", p), q))), D(0));
        Formula unique = Seq(Exists, Bang, Sp, Typed(q, Reals()), Comma, Sp,
            Parenthesized(And(interval, zero)));
        return IffOf(Named("claim"), All("M", Naturals(), Implies(AtMost(D(1), F.Id("M")),
            All("p", Distributions(), Implies(Call("IsDegreeDistribution", p),
                Implies(Less(D(0), Call("meanDegree", p)),
                    Implies(Less(D(1), Call("excessRatio", p)), unique)))))));
    }
}
