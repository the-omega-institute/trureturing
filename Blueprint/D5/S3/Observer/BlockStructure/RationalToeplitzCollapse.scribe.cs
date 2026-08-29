using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class RationalToeplitzCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common denominator converts a rational feature Gram matrix into a congruence "
            + "of one weighted monomial moment matrix.",
        H("Rational-Toeplitz Collapse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-feature-gram-collapses-to-one-moment-matrix"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/RationalToeplitzCollapse."
                        + "rational_toeplitz_collapse"),
                H("A common denominator gives one moment congruence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite positive measure on the unit circle, a complex coefficient "
                            + "matrix, and a polynomial without unit-circle zeros construct "
                            + "the monomial and rational feature vectors.")),
                    Paragraph(Text(
                        "The weighted measure uses the reciprocal norm-square of the supplied "
                            + "denominator. Compactness of the circle and nonvanishing of the "
                            + "denominator make this measure finite.")),
                    Paragraph(Text(
                        "Expanding both finite matrix products and moving their scalar "
                            + "coefficients through the integral identifies the rational Gram "
                            + "matrix with the displayed congruence."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula circle = F.Id("Circle");
        Formula n = F.Id("n");
        Formula index = Call("Fin", n);
        Formula matrixType = Call("Matrix", index, index, complex);
        Formula polynomialType = Call("Polynomial", complex);
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula measure = Call("Measure", circle);
        Formula mu = F.Id("mu");
        Formula coefficient = F.Id("A");
        Formula denominator = F.Id("D");
        Formula denominatorWitness = F.Id("hD");
        Formula monomial = F.Id("v");
        Formula feature = Psi;
        Formula weighted = Sigma;
        Formula gram = F.Id("G");
        Formula moment = F.Id("T");
        Formula z = F.Id("z");
        Formula i = F.Id("i");
        Formula j = F.Id("j");

        Formula denominatorAt = Call("eval", denominator, z);
        Formula denominatorNonzero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", circle)],
            Seq(denominatorAt, Sp, Neq, Sp, D(0)));
        Formula monomialDefinition = Seq(
            Typed(monomial, Arrow(circle, Arrow(index, complex))), Comma, Sp,
            Forall, Sp, Typed(z, circle), Comma, Sp, Typed(j, index), Comma, Sp,
            Apply(Apply(monomial, z), j), Sp, Eq, Sp,
            new Formula.Power(z, j));
        Formula featureDefinition = Seq(
            Typed(feature, Arrow(circle, Arrow(index, complex))), Comma, Sp,
            Forall, Sp, Typed(z, circle), Comma, Sp, Typed(i, index), Comma, Sp,
            Apply(Apply(feature, z), i), Sp, Eq, Sp,
            new Formula.Fraction(
                Apply(Call("mulVec", coefficient, Apply(monomial, z)), i),
                denominatorAt));
        Formula density = Call("ofReal", new Formula.Power(
            Call("normSq", denominatorAt), Seq(Minus, D(1))));
        Formula weightedDefinition = Seq(
            Typed(weighted, measure), Sp, Eq, Sp,
            Call("withDensity", mu, Lambda(Typed(z, circle), density)));
        Formula gramDefinition = MatrixDefinition(
            gram, matrixType, index, i, j,
            Call("integral", mu, Lambda(Typed(z, circle),
                Seq(Apply(Apply(feature, z), i), Sp, Cdot, Sp,
                    StarOf(Apply(Apply(feature, z), j))))));
        Formula momentDefinition = MatrixDefinition(
            moment, matrixType, index, i, j,
            Call("integral", weighted, Lambda(Typed(z, circle),
                Seq(Apply(Apply(monomial, z), i), Sp, Cdot, Sp,
                    StarOf(Apply(Apply(monomial, z), j))))));
        Formula letObjects = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            monomialDefinition, SemiSpace,
            featureDefinition, SemiSpace,
            weightedDefinition, SemiSpace,
            gramDefinition, SemiSpace,
            momentDefinition, Close);
        Formula conclusion = Seq(
            gram, Sp, Eq, Sp,
            coefficient, Sp, Cdot, Sp, moment, Sp, Cdot, Sp,
            Call("conjTranspose", coefficient));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(n, natural), Comma, Sp,
                Typed(mu, finiteMeasure), Comma),
            Seq(Typed(coefficient, matrixType), Comma, Sp,
                Typed(denominator, polynomialType), Comma),
            Seq(Typed(denominatorWitness, denominatorNonzero), Comma),
            Seq(letObjects, Comma),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula MatrixDefinition(
        Formula matrix,
        Formula matrixType,
        Formula indexType,
        Formula i,
        Formula j,
        Formula value) =>
        Seq(
            Typed(matrix, matrixType), Comma, Sp,
            Forall, Sp, Typed(i, indexType), Comma, Sp, Typed(j, indexType), Comma, Sp,
            new Formula.Subscript(matrix, Seq(i, Comma, j)), Sp, Eq, Sp, value);

    private static Formula StarOf(Formula value) =>
        Seq(Grp(value), Caret, Grp(Star));

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
}
