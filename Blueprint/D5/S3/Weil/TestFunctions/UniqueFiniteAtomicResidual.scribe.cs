using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class UniqueFiniteAtomicResidualDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/UniqueFiniteAtomicResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A represented truncated moment vector has an attained greatest Haar floor. Its singular "
            + "residual has one rank-atomic measure and one maximal weighted completion.",
        H("Unique Finite-Atomic Residual"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-finite-atomic-residual"),
            DeclarationHandle.Create(Handle + "unique_finite_atomic_residual"),
            H("Unique finite-atomic residual"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The feasible floor coefficients are those dominated by a representing "
                        + "measure, and the distinguished coefficient is their supremum. The "
                        + "exact floor theorem identifies it with the least Toeplitz eigenvalue.")),
                Paragraph(Text(
                    "After subtracting that attained greatest coefficient, the residual measure "
                        + "is constructed from the positive semidefinite truncated moment matrix. "
                        + "A unit kernel vector confines its support to the contact roots.")),
                Paragraph(Text(
                    "Lagrange interpolation makes every representing measure agree on each "
                        + "root mass, proving uniqueness. Removing zero masses leaves positive "
                        + "distinct atoms, while a weighted Vandermonde Gram factorization "
                        + "identifies their number with the Toeplitz rank.")),
                Paragraph(Text(
                    "Multiplication by the denominator norm-square density constructs the maximal "
                        + "completion at the distinguished coefficient. Residual uniqueness gives "
                        + "completion uniqueness, and Dirac density gives the weighted atomic sum."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nonnegativeReal = Call("NonnegativeReal");
        Formula circle = Call("Circle");
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula depth = F.Id("N");
        Formula sourceMoment = F.Id("m");
        Formula residualMoment = F.Id("mStar");
        Formula exponent = F.Id("ell");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula circlePoint = F.Id("z");
        Formula vector = F.Id("v");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula alphaStar = F.Id("alphaStar");
        Formula totalMass = F.Id("R");
        Formula denominator = F.Id("D");
        Formula toeplitz = F.Id("Tstar");
        Formula residual = F.Id("tau");
        Formula candidate = F.Id("rho");
        Formula point = F.Id("point");
        Formula weight = F.Id("weight");
        Formula atom = F.Id("a");
        Formula completion = F.Id("muStar");
        Formula completionCandidate = F.Id("nu");
        Formula finDepth = Call("Fin", Add(depth, D(1)));
        Formula matrixType = Call("Matrix", finDepth, finDepth, complex);
        Formula toeplitzRank = Call("rank", toeplitz);
        Formula finRank = Call("Fin", toeplitzRank);

        Formula Lambda(Formula variable, Formula body) =>
            Seq(Open, variable, Sp, Mapsto, Sp, body, Close);
        Formula Let(Formula name, Formula value) =>
            Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value);
        Formula SourceMomentAt(Formula index) => Apply(sourceMoment, index);
        Formula ResidualMomentAt(Formula index) => Apply(residualMoment, index);
        Formula MonomialAt(Formula index) =>
            Call("zpow", circlePoint, Call("neg", index));
        Formula SourceMomentAgreement(Formula measure) => ForAll(
            [Bound("ell", integer)],
            Implies(
                LessEqual(Call("natAbs", exponent), depth),
                Equal(
                    Call("integral", circlePoint, circle, MonomialAt(exponent), measure),
                    SourceMomentAt(exponent))));
        Formula ResidualMomentAgreement(Formula measure) => ForAll(
            [Bound("ell", integer)],
            Implies(
                LessEqual(Call("natAbs", exponent), depth),
                Equal(
                    Call("integral", circlePoint, circle, MonomialAt(exponent), measure),
                    ResidualMomentAt(exponent))));
        Formula FloorFeasible(Formula coefficient) => Exists(
            [Bound("mu", finiteMeasure)],
            All(
                SourceMomentAgreement(F.Id("mu")),
                LessEqual(
                    Call(
                        "toMeasure",
                        Call("smul", coefficient, Call("normalizedCircleHaar"))),
                    Call("toMeasure", F.Id("mu")))));
        Formula DensityAt(Formula location) =>
            Call("ofReal", Call("normSq", Apply(denominator, location)));
        Formula AtomicSum() => Call(
            "sum",
            atom,
            finRank,
            Call("smul", Apply(weight, atom), Call("dirac", Apply(point, atom))));
        Formula WeightedAtomicSum() => Call(
            "sum",
            atom,
            finRank,
            Call(
                "smul",
                Mul(Apply(weight, atom), DensityAt(Apply(point, atom))),
                Call("dirac", Apply(point, atom))));
        Formula CompletionRelation(Formula measure) => Exists(
            [Bound("tau", finiteMeasure)],
            All(
                ResidualMomentAgreement(residual),
                Equal(
                    Call("toMeasure", measure),
                    Add(
                        Call(
                            "toMeasure",
                            Call("smul", alphaStar, Call("normalizedCircleHaar"))),
                        Call(
                            "withDensity",
                            Call("toMeasure", residual),
                            Lambda(circlePoint, DensityAt(circlePoint)))))));

        Formula sourceHermitian = ForAll(
            [Bound("ell", integer)],
            Equal(
                SourceMomentAt(Call("neg", exponent)),
                Call("star", SourceMomentAt(exponent))));
        Formula zeroMoment = Equal(SourceMomentAt(D(0)), totalMass);
        Formula positiveMass = Less(D(0), totalMass);
        Formula represented = Exists(
            [Bound("mu", finiteMeasure)],
            SourceMomentAgreement(F.Id("mu")));
        Formula alphaStarDefinition = Let(
            alphaStar,
            Call("sSup", Call("setOf", Lambda(alpha, FloorFeasible(alpha)))));
        Formula residualMomentDefinition = Let(
            residualMoment,
            Lambda(
                exponent,
                Sub(
                    SourceMomentAt(exponent),
                    Call("ite", Equal(exponent, D(0)), alphaStar, D(0)))));
        Formula matrixLambda = Lambda(
            Seq(row, Comma, column, InMacro, finDepth),
            ResidualMomentAt(Sub(Call("toInt", row), Call("toInt", column))));
        Formula matrix = Call("Matrix", matrixLambda);
        Formula sourceMatrixLambda = Lambda(
            Seq(row, Comma, column, InMacro, finDepth),
            SourceMomentAt(Sub(Call("toInt", row), Call("toInt", column))));
        Formula sourceMatrix = Call("Matrix", sourceMatrixLambda);
        Formula positive = Call("PosSemidef", matrix);
        Formula unitVector = Equal(
            Call("dotProduct", Call("star", vector), vector),
            D(1));
        Formula singularKernel = Equal(
            Call("mulVec", matrix, vector),
            D(0));
        Formula toeplitzDefinition = Let(toeplitz, matrix);
        Formula alphaStarAttained = FloorFeasible(alphaStar);
        Formula maximalFloor = All(
            alphaStarAttained,
            ForAll(
                [Bound("beta", nonnegativeReal)],
                Implies(FloorFeasible(beta), LessEqual(beta, alphaStar))));
        Formula exactFloor = Equal(
            alphaStar,
            Call("smallestEigenvalue", sourceMatrix));
        Formula residualUnique = ForAll(
            [Bound("rho", finiteMeasure)],
            Implies(
                ResidualMomentAgreement(candidate),
                Equal(candidate, residual)));
        Formula pointInjective = Call("Injective", point);
        Formula positiveWeights = ForAll(
            [Bound("a", finRank)],
            Less(D(0), Apply(weight, atom)));
        Formula atomicResidual = Equal(
            Call("toMeasure", residual),
            AtomicSum());
        Formula completionUnique = ForAll(
            [Bound("nu", finiteMeasure)],
            Implies(
                CompletionRelation(completionCandidate),
                Equal(completionCandidate, completion)));
        Formula completionFormula = Equal(
            Call("toMeasure", completion),
            Add(
                Call(
                    "toMeasure",
                    Call("smul", alphaStar, Call("normalizedCircleHaar"))),
                WeightedAtomicSum()));
        Formula completionWitness = Exists(
            [Bound("muStar", finiteMeasure)],
            All(
                CompletionRelation(completion),
                completionUnique,
                completionFormula));
        Formula atomicWitness = Exists(
            [
                Bound("point", Arrow(finRank, circle)),
                Bound("weight", Arrow(finRank, nonnegativeReal)),
            ],
            All(
                pointInjective,
                positiveWeights,
                atomicResidual,
                completionWitness));
        Formula residualWitness = Exists(
            [Bound("tau", finiteMeasure)],
            All(
                ResidualMomentAgreement(residual),
                residualUnique,
                atomicWitness));
        Formula premise = All(
            sourceHermitian,
            zeroMoment,
            positiveMass,
            represented,
            alphaStarDefinition,
            residualMomentDefinition,
            toeplitzDefinition,
            alphaStarAttained,
            positive,
            unitVector,
            singularKernel);
        Formula conclusion = All(
            maximalFloor,
            exactFloor,
            residualWitness);

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("m", Arrow(integer, complex)),
                Bound("R", real),
                Bound("v", Arrow(finDepth, complex)),
                Bound("D", Call("ContinuousMap", circle, complex)),
            ],
            Implies(premise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
