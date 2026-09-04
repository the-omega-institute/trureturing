using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class FiniteCommonSpectrumCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite rational-feature Gram exists exactly when its inverse coefficient "
            + "congruence is a positive Hermitian Toeplitz matrix.",
        H("Finite Common-Spectrum Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-rational-gram-positive-toeplitz-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/FiniteCommonSpectrumCriterion."
                        + "finite_common_spectrum_criterion"),
                H("Finite rational Grams are exactly positive Toeplitz transforms"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The supplied invertible coefficient matrix and polynomial without "
                            + "unit-circle zeros construct the complete common-denominator "
                            + "rational feature family.")),
                    Paragraph(Text(
                        "The forward implication applies the rational Gram congruence after "
                            + "reciprocal denominator weighting and circle reflection.")),
                    Paragraph(Text(
                        "For the converse, the truncated Toeplitz moment theorem constructs a "
                            + "finite positive circle measure. Restoring the denominator weight "
                            + "and cancelling the invertible congruence recovers the given Gram.")),
                    Paragraph(Text(
                        "Conjugate symmetry of the displayed moment sequence is the public "
                            + "Hermitian condition. No separate Hermitian premise on the given "
                            + "matrix is needed because either side of the equivalence forces it."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula circle = F.Id("Circle");
        Formula depth = F.Id("N");
        Formula index = Call("Fin", Seq(depth, Sp, Plus, Sp, D(1)));
        Formula matrixType = Call("Matrix", index, index, complex);
        Formula polynomialType = Call("Polynomial", complex);
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula momentType = Arrow(integers, complex);

        Formula coefficient = F.Id("A");
        Formula denominator = F.Id("D");
        Formula gram = F.Id("G");
        Formula monomial = F.Id("v");
        Formula feature = Psi;
        Formula rationalGram = F.Id("Gram");
        Formula transformed = F.Id("T");
        Formula mu = F.Id("mu");
        Formula moment = F.Id("y");
        Formula z = F.Id("z");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");

        Formula denominatorAt(Formula point) => Call("eval", denominator, point);
        Formula monomialAt = Lambda(
            Typed(z, circle),
            Lambda(
                Typed(j, index),
                new Formula.Power(z, Call("toNat", j))));
        Formula featureAt = Lambda(
            Typed(z, circle),
            Lambda(
                Typed(i, index),
                new Formula.Fraction(
                    Apply(Call("mulVec", coefficient, Apply(monomial, z)), i),
                    denominatorAt(z))));
        Formula gramAt = Lambda(
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
                            Product(
                                Apply(Apply(feature, z), i),
                                Call("star", Apply(Apply(feature, z), j))),
                            mu)))));
        Formula inverseCoefficient = Call("inv", coefficient);

        Formula monomialDefinition = LetTyped(
            monomial, Arrow(circle, Arrow(index, complex)), monomialAt);
        Formula featureDefinition = LetTyped(
            feature, Arrow(circle, Arrow(index, complex)), featureAt);
        Formula gramDefinition = LetTyped(
            rationalGram, Arrow(finiteMeasure, matrixType), gramAt);
        Formula transformedDefinition = LetTyped(
            transformed,
            matrixType,
            Product(
                inverseCoefficient,
                gram,
                Call("conjTranspose", inverseCoefficient)));
        Formula letObjects = new Formula.Aligned([
            monomialDefinition,
            featureDefinition,
            gramDefinition,
            transformedDefinition,
        ]);

        Formula measureWitness = ExistsMany(
            [Bound("mu", finiteMeasure)],
            Equal(gram, Apply(rationalGram, mu)));
        Formula hermitianSequence = ForAllMany(
            [Bound("k", integers)],
            Equal(
                Apply(moment, Grp(Minus, k)),
                Call("star", Apply(moment, k))));
        Formula toeplitzRepresentation = Equal(
            transformed,
            Call("toeplitzMatrix", moment, depth));
        Formula transformedCondition = And(
            Call("PosSemidef", transformed),
            ExistsMany(
                [Bound("y", momentType)],
                And(hermitianSequence, toeplitzRepresentation)));
        Formula conclusion = new Formula.Logic(
            measureWitness, FormulaLogicOperator.Iff, transformedCondition);
        Formula denominatorNonzero = ForAllMany(
            [Bound("z", circle)],
            Seq(denominatorAt(z), Sp, Neq, Sp, D(0)));
        Formula body = Seq(letObjects, Comma, RowBreak, Grp(), conclusion);

        return Disp(ForAllMany(
            [
                Bound("N", natural),
                Bound("A", matrixType),
                Bound("hA", Call("IsUnit", coefficient)),
                Bound("D", polynomialType),
                Bound("hD", denominatorNonzero),
                Bound("G", matrixType),
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

    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

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

    private static Formula ForAllMany(
        IReadOnlyList<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(
        IReadOnlyList<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
