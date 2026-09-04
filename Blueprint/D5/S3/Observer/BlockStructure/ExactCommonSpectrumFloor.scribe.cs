using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class ExactCommonSpectrumFloorDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/BlockStructure/ExactCommonSpectrumFloor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest common normalized-Haar component of a rational feature Gram "
            + "matrix is the least eigenvalue in either whitened coordinate system.",
        H("Exact Common-Spectrum Floor"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-common-spectrum-floor"),
            DeclarationHandle.Create(Handle + "exact_common_spectrum_floor"),
            H("The exact floor is the common least eigenvalue"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The feature family, its rational Gram matrix, the reflected "
                        + "weighted moment matrix, and both congruent reference "
                        + "matrices are constructed from the supplied coefficient "
                        + "matrix, denominator, and finite circle measure.")),
                Paragraph(Text(
                    "The forward direction subtracts a dominated normalized-Haar "
                        + "component. The reverse direction represents the positive "
                        + "Toeplitz residual by a finite circle measure, reverses the "
                        + "circle coordinate, and restores the denominator weight.")),
                Paragraph(Text(
                    "Positive-definite whitening identifies the greatest feasible "
                        + "real floor with the last ordered Hermitian eigenvalue. "
                        + "Invertible congruence gives the same value for the original "
                        + "Gram matrix and its reference matrix."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula nonnegativeReal = F.Id("NonnegativeReal");
        Formula circle = F.Id("Circle");
        Formula n = F.Id("N");
        Formula index = Call("Fin", Add(n, D(1)));
        Formula matrixType = Call("Matrix", index, index, complex);
        Formula polynomialType = Call("Polynomial", complex);
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula measureType = Call("Measure", circle);

        Formula coefficient = F.Id("A");
        Formula denominator = F.Id("D");
        Formula gram = F.Id("G");
        Formula source = F.Id("mu0");
        Formula z = F.Id("z");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula gramHermitian = F.Id("hG");
        Formula hT = F.Id("hT");
        Formula hQD = F.Id("hQD");
        Formula hQB = F.Id("hQB");

        Formula monomial = F.Id("v");
        Formula feature = Psi;
        Formula rationalGram = F.Id("Gram");
        Formula density = F.Id("wD");
        Formula weightedReflected = F.Id("weightedReflected");
        Formula momentMatrix = F.Id("M");
        Formula haarMoment = new Formula.Subscript(F.Id("H"), denominator);
        Formula referenceGram = F.Id("B");
        Formula transformedGram = F.Id("T");
        Formula feasible = F.Id("F");
        Formula alphaStar = F.Id("alphaStar");
        Formula whiteningD = new Formula.Subscript(F.Id("W"), denominator);
        Formula whitenedD = new Formula.Subscript(F.Id("Q"), denominator);
        Formula whiteningB = new Formula.Subscript(F.Id("W"), referenceGram);
        Formula whitenedB = new Formula.Subscript(F.Id("Q"), referenceGram);

        Formula denominatorAt = Call("eval", denominator, z);
        Formula monomialAt = Lambda(
            Typed(z, circle),
            Lambda(Typed(j, index), new Formula.Power(z, Call("toNat", j))));
        Formula featureAt(Formula point, Formula coordinate) =>
            new Formula.Fraction(
                Apply(Call("mulVec", coefficient, Apply(monomial, point)), coordinate),
                Call("eval", denominator, point));
        Formula rawFeatureAt(Formula point, Formula coordinate) =>
            new Formula.Fraction(
                Apply(
                    Call(
                        "mulVec",
                        coefficient,
                        Lambda(
                            Typed(k, index),
                            new Formula.Power(point, Call("toNat", k)))),
                    coordinate),
                Call("eval", denominator, point));
        Formula rawSourceGram = ForAll(
            [Bound("i", index), Bound("j", index)],
            Equal(
                Call(
                    "integral",
                    z,
                    circle,
                    Seq(
                        rawFeatureAt(z, i), Sp, Cdot, Sp,
                        Call("star", rawFeatureAt(z, j))),
                    source),
                Apply(gram, i, j)));

        Formula monomialDefinition = LetTyped(
            monomial, Arrow(circle, Arrow(index, complex)), monomialAt);
        Formula featureDefinition = LetTyped(
            feature,
            Arrow(circle, Arrow(index, complex)),
            Lambda(Typed(z, circle), Lambda(Typed(i, index), featureAt(z, i))));
        Formula gramDefinition = LetTyped(
            rationalGram,
            Arrow(finiteMeasure, matrixType),
            Lambda(
                Typed(mu, finiteMeasure),
                Call(
                    "Matrix",
                    Lambda(
                        Typed(i, index),
                        Lambda(
                            Typed(j, index),
                            Call(
                                "integral",
                                z,
                                circle,
                                Seq(
                                    Apply(Apply(feature, z), i), Sp, Cdot, Sp,
                                    Call("star", Apply(Apply(feature, z), j))),
                                mu))))));
        Formula densityDefinition = LetTyped(
            density,
            Arrow(circle, F.Id("ENNReal")),
            Lambda(
                Typed(z, circle),
                Call(
                    "ofReal",
                    Call("inv", Call("normSq", Call("eval", denominator, z))))));
        Formula weightedDefinition = LetTyped(
            weightedReflected,
            Arrow(finiteMeasure, measureType),
            Lambda(
                Typed(mu, finiteMeasure),
                Call(
                    "map",
                    F.Id("inv"),
                    Call("withDensity", Call("toMeasure", mu), density))));
        Formula momentDefinition = LetTyped(
            momentMatrix,
            Arrow(finiteMeasure, matrixType),
            Lambda(
                Typed(mu, finiteMeasure),
                Call(
                    "toeplitzMatrix",
                    Call("circleMoment", Apply(weightedReflected, mu)),
                    n)));
        Formula haarMomentDefinition = LetTyped(
            haarMoment, matrixType, Apply(momentMatrix, Call("normalizedCircleHaar")));
        Formula referenceDefinition = LetTyped(
            referenceGram,
            matrixType,
            Product(coefficient, haarMoment, Call("conjTranspose", coefficient)));
        Formula inverseA = Call("inv", coefficient);
        Formula transformedDefinition = LetTyped(
            transformedGram,
            matrixType,
            Product(inverseA, gram, Call("conjTranspose", inverseA)));
        Formula feasiblePredicate = Exists(
            [Bound("mu", finiteMeasure)],
            All(
                Equal(Apply(rationalGram, mu), gram),
                LessEqual(
                    Call(
                        "toMeasure",
                        Call("smul", alpha, Call("normalizedCircleHaar"))),
                    Call("toMeasure", mu))));
        Formula feasibleDefinition = LetTyped(
            feasible,
            Call("Set", nonnegativeReal),
            new Formula.SetBuilder(feasiblePredicate, alpha, nonnegativeReal));
        Formula alphaDefinition = LetTyped(alphaStar, nonnegativeReal, Call("sSup", feasible));
        Formula hTDefinition = LetTyped(
            hT,
            Call("IsHermitian", transformedGram),
            Call(
                "isHermitianConjTransposeMulMul",
                Call("conjTranspose", inverseA),
                gramHermitian));
        Formula whiteningDDefinition = LetTyped(
            whiteningD, matrixType, Call("inv", Call("sqrt", haarMoment)));
        Formula whitenedDDefinition = LetTyped(
            whitenedD,
            matrixType,
            Product(Call("conjTranspose", whiteningD), transformedGram, whiteningD));
        Formula hQDDefinition = LetTyped(
            hQD,
            Call("IsHermitian", whitenedD),
            Call("isHermitianConjTransposeMulMul", whiteningD, hT));
        Formula whiteningBDefinition = LetTyped(
            whiteningB, matrixType, Call("inv", Call("sqrt", referenceGram)));
        Formula whitenedBDefinition = LetTyped(
            whitenedB,
            matrixType,
            Product(Call("conjTranspose", whiteningB), gram, whiteningB));
        Formula hQBDefinition = LetTyped(
            hQB,
            Call("IsHermitian", whitenedB),
            Call("isHermitianConjTransposeMulMul", whiteningB, gramHermitian));

        Formula feasibleReal = new Formula.SetBuilder(
            Call(
                "PosSemidef",
                Call(
                    "sub",
                    transformedGram,
                    Call("smul", Call("toComplex", alpha), haarMoment))),
            alpha,
            real);
        Formula greatest = Call(
            "IsGreatest", feasibleReal, Call("toReal", alphaStar));
        Formula lastIndex = Call("last", n);
        Formula firstEigenvalue = Equal(
            Call("toReal", alphaStar),
            Call("eigenvalues0", whitenedD, hQD, lastIndex));
        Formula secondEigenvalue = Equal(
            Call("toReal", alphaStar),
            Call("eigenvalues0", whitenedB, hQB, lastIndex));
        Formula conclusion = All(greatest, firstEigenvalue, secondEigenvalue);

        Formula denominatorNonzero = ForAll(
            [Bound("z", circle)],
            Seq(Call("eval", denominator, z), Sp, Neq, Sp, D(0)));
        Formula letObjects = new Formula.Aligned([
            monomialDefinition,
            featureDefinition,
            gramDefinition,
            densityDefinition,
            weightedDefinition,
            momentDefinition,
            haarMomentDefinition,
            referenceDefinition,
            transformedDefinition,
            feasibleDefinition,
            alphaDefinition,
        ]);
        Formula spectralObjects = new Formula.Aligned([
            hTDefinition,
            whiteningDDefinition,
            whitenedDDefinition,
            hQDDefinition,
            whiteningBDefinition,
            whitenedBDefinition,
            hQBDefinition,
        ]);
        Formula body = Seq(
            letObjects,
            Comma,
            RowBreak,
            Grp(),
            ForAll(
                [Bound("hHD", Call("PosDef", haarMoment))],
                Seq(spectralObjects, Comma, RowBreak, Grp(), conclusion)));

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("A", matrixType),
                Bound("D", polynomialType),
                Bound("G", matrixType),
                Bound("mu0", finiteMeasure),
                Bound("hA", Call("IsUnit", coefficient)),
                Bound("hD", denominatorNonzero),
                Bound("hG", Call("IsHermitian", gram)),
                Bound("hSource", rawSourceGram),
            ],
            body));
    }

    private static Formula LetTyped(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(name, type), Sp, Eq, Sp, value, SemiSpace);

    private static Formula Product(params Formula[] factors)
    {
        var items = new List<Formula>();
        for (var index = 0; index < factors.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Cdot, Sp]);
            items.Add(factors[index]);
        }

        return Seq([.. items]);
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula All(params Formula[] clauses) =>
        clauses.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
