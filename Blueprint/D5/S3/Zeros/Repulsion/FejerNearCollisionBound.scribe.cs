using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Repulsion;

internal sealed class FejerNearCollisionBoundDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Zeros/Repulsion/FejerNearCollisionBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fejer kernels give exact Fourier energy identities and explicit collision bounds.",
        H("Finite Fejer Near-Collision Bounds"),
        Blocks(
            Paragraph(Text(
                "For M at least one, F_M is the Fejer cosine polynomial, S_M(t) is "
                    + "the length-M exponential sum, E_M(gamma) is the ordered pair "
                    + "energy, N_M(gamma) is the filtered ordered near-pair set, and "
                    + "mult_gamma(v) is the cardinality of the fiber gamma^{-1}(v).")),
            Describe.Lean(
                DescribeId.Create("finite-fejer-square"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_square"),
                H("The Fejer kernel is a normalized square"),
                StatementSource.FromAuthor(FejerSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural M and real t, the Fejer kernel equals "
                            + "one over M times the squared norm of the geometric exponential sum.")),
                    Paragraph(Text(
                        "The proof grows the exponential sum by one endpoint. Expanding the "
                            + "new norm square produces the next triangular autocorrelation row; "
                            + "normalization then gives the stated Fejer polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-fejer-energy-identity"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_energy_identity"),
                H("Pair energy is signed Fourier energy"),
                StatementSource.FromAuthor(FejerEnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a family indexed by Fin n, the total ordered pair energy is "
                            + "the sum over every integer mode with absolute value below M, "
                            + "weighted by 1-|k|/M, of the squared exponential-sum norm.")),
                    Paragraph(Text(
                        "The proof partitions the signed finite sum into its zero, positive, "
                            + "and negative ranges. Each cosine pair sum becomes a complex norm "
                            + "square, and conjugation identifies the two nonzero signs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fejer-local-explicit-lower-bound"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_local_lower_bound"),
                H("The Fejer kernel is large on its central window"),
                StatementSource.FromAuthor(FejerLocalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Inside |t| <= pi/M, the Fejer kernel is at least 4M/pi^2.")),
                    Paragraph(Text(
                        "The proof treats t=0 directly and otherwise combines the geometric-sum "
                            + "identity with the lower sine estimate on [-pi/2,pi/2] and the "
                            + "global upper estimate |sin y| <= |y|. Squaring yields the exact "
                            + "constant 4/pi^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-near-pair-count-bound"),
                DeclarationHandle.Create(DeclarationPrefix + "near_pair_count_bound"),
                H("Fejer energy controls ordered near collisions"),
                StatementSource.FromAuthor(NearPairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The number of ordered pairs separated by at most pi/M is bounded by "
                            + "pi^2/(4M) times the total Fejer energy.")),
                    Paragraph(Text(
                        "The proof sums the local lower bound over the filtered near-pair set, "
                            + "then uses the global square representation to add the nonnegative "
                            + "contribution of every remaining ordered pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-multiplicity-energy-lower-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "distinct_multiplicity_energy_lower_bound"),
                H("Fejer energy dominates squared multiplicities"),
                StatementSource.FromAuthor(MultiplicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The total energy is at least M times the sum of squared fiber "
                            + "multiplicities over the distinct values attained by gamma.")),
                    Paragraph(Text(
                        "Equal-value ordered pairs form disjoint fiber blocks. On every such "
                            + "block the argument is zero and F_M(0)=M; fiberwise reindexing "
                            + "turns the resulting index sum into the displayed distinct-value sum.")),
                    Paragraph(Text(
                        "This finite deterministic inequality supplies no zeta-zero asymptotic "
                            + "and no positive proportion of simple zeros without a separate "
                            + "upper bound for the Fejer energy."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula NormSquare(Formula value) =>
        Power(new Formula.Norm(value), D(2));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula FamilyDomain(Formula n) =>
        new Formula.TypeArrow(Fin(n), Reals());

    private static Formula GammaAt(Formula index) =>
        new Formula.Subscript(GammaLower, index);

    private static Formula Fejer(Formula m, Formula t) =>
        Call("F", m, t);

    private static Formula ExponentialSum(Formula m, Formula t) =>
        Call("S", m, t);

    private static Formula PairEnergy(Formula m) => Call("E", m, GammaLower);

    private static Formula NearPairs(Formula m) => Call("N", m, GammaLower);

    private static Formula Multiplicity(Formula value) =>
        Call("mult", GammaLower, value);

    private static Formula IndexedSum(Formula condition, Formula body) =>
        Seq(Sum, Underscore, Grp(condition), Sp, body);

    private static Formula FejerSquareFormula()
    {
        Formula m = F.Id("M");
        Formula t = F.Id("t");
        Formula premise = LessEqual(D(1), m);
        Formula square = Equal(
            Fejer(m, t),
            Multiply(Divide(D(1), m), NormSquare(ExponentialSum(m, t))));
        return Disp(ForAll(
            [Bound("M", Naturals()), Bound("t", Reals())],
            Implies(premise, square)));
    }

    private static Formula FejerEnergyFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula family = GammaLower;
        Formula modeCondition = And(
            new Formula.Relation(k, FormulaRelationOperator.MemberOf, Integers()),
            new Formula.Relation(Absolute(k), FormulaRelationOperator.LessThan, m));
        Formula weight = Subtract(D(1), Divide(Absolute(k), m));
        Formula phaseSum = IndexedSum(
            new Formula.Relation(i, FormulaRelationOperator.MemberOf, Fin(n)),
            Call("phase", Multiply(k, GammaAt(i))));
        Formula signedEnergy = IndexedSum(
            modeCondition,
            Multiply(weight, NormSquare(phaseSum)));
        Formula premise = LessEqual(D(1), m);
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound("gamma", FamilyDomain(n))],
            Implies(premise, Equal(PairEnergy(m), signedEnergy))));
    }

    private static Formula FejerLocalFormula()
    {
        Formula m = F.Id("M");
        Formula t = F.Id("t");
        Formula premise = And(
            LessEqual(D(1), m),
            LessEqual(Absolute(t), Divide(Pi, m)));
        Formula lowerBound = LessEqual(
            Divide(Multiply(D(4), m), Power(Pi, D(2))),
            Fejer(m, t));
        return Disp(ForAll(
            [Bound("M", Naturals()), Bound("t", Reals())],
            Implies(premise, lowerBound)));
    }

    private static Formula NearPairFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula premise = LessEqual(D(1), m);
        Formula coefficient = Divide(Power(Pi, D(2)), Multiply(D(4), m));
        Formula conclusion = LessEqual(
            Call("card", NearPairs(m)),
            Multiply(coefficient, PairEnergy(m)));
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound("gamma", FamilyDomain(n))],
            Implies(premise, conclusion)));
    }

    private static Formula MultiplicityFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula v = F.Id("v");
        Formula premise = LessEqual(D(1), m);
        Formula imageCondition = new Formula.Relation(
            v, FormulaRelationOperator.MemberOf, Call("image", GammaLower));
        Formula mass = IndexedSum(imageCondition, Power(Multiplicity(v), D(2)));
        Formula conclusion = LessEqual(Multiply(m, mass), PairEnergy(m));
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound("gamma", FamilyDomain(n))],
            Implies(premise, conclusion)));
    }
}
