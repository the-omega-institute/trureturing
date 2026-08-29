using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class RationalContactSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gram-kernel contact polynomial vanishes on the positive residual support of a "
            + "rational unit-circle completion.",
        H("Rational Contact Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-contact-polynomial-localizes-residual-support"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/RationalContactSupport."
                        + "rational_contact_support"),
                H("Kernel contact polynomials vanish on residual support"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed statement constructs every source object. Polynomial "
                            + "numerators and a denominator without unit-circle zeros determine "
                            + "the rational feature vector, while normalized Haar and an "
                            + "arbitrary finite positive residual determine the completion.")),
                    Paragraph(Text(
                        "Both complex Gram matrices are displayed entrywise as integrals on the "
                            + "exact unit-circle carrier. The contact polynomial is the conjugate-"
                            + "coefficient combination of the supplied polynomial numerators.")),
                    Paragraph(Text(
                        "The completion Gram matrix splits into its normalized-Haar floor and "
                            + "residual Gram matrix. A kernel vector therefore has zero residual "
                            + "quadratic form, hence its squared contact function vanishes almost "
                            + "everywhere.")),
                    Paragraph(Text(
                        "Polynomial evaluation is continuous, so its zero set is closed. The "
                            + "almost-everywhere vanishing statement therefore places the full "
                            + "support of the completion residual inside that zero set."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula nonnegativeReal = Seq(
            Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, D(0)));
        Formula circle = F.Id("Circle");
        Formula n = F.Id("n");
        Formula index = Call("Fin", n);
        Formula polynomial = Call("Polynomial", complex);
        Formula numerator = F.Id("p");
        Formula denominator = F.Id("D");
        Formula denominatorWitness = F.Id("hD");
        Formula alpha = Alpha;
        Formula residual = F.Id("tau");
        Formula feature = Seq(Psi);
        Formula completion = F.Id("muStar");
        Formula gram = F.Id("G");
        Formula haarGram = F.Id("B");
        Formula contactPolynomial = F.Id("P");
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula z = F.Id("z");
        Formula vectorType = Arrow(index, complex);
        Formula matrixType = Call("Matrix", index, index, complex);
        Formula finiteCircleMeasure = Call("FiniteMeasure", circle);
        Formula haar = Call("normalizedCircleHaar");

        Formula denominatorAtZ = Call("eval", denominator, z);
        Formula numeratorAt = Call("eval", Apply(numerator, i), z);
        Formula denominatorNonzero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", circle)],
            Seq(denominatorAtZ, Sp, Neq, Sp, D(0)));
        Formula featureAt = Apply(Apply(feature, z), i);
        Formula featureDefinition = Seq(
            Typed(feature, Arrow(circle, Arrow(index, complex))), Comma, Sp,
            Forall, Sp, Typed(z, circle), Comma, Sp, Typed(i, index), Comma, Sp,
            featureAt, Sp, Eq, Sp,
            new Formula.Fraction(numeratorAt, denominatorAtZ));
        Formula completionDefinition = Seq(
            Typed(completion, finiteCircleMeasure), Sp, Eq, Sp,
            alpha, Sp, Cdot, Sp, haar, Sp, Plus, Sp, residual);

        Formula featureI = Apply(Apply(feature, z), i);
        Formula featureJStar = Seq(
            Grp(Apply(Apply(feature, z), j)), Caret, Grp(Star));
        Formula gramIntegrand = Seq(featureI, Sp, featureJStar);
        Formula gramDefinition = MatrixDefinition(
            gram, matrixType, index, i, j,
            Call("integral", completion,
                Lambda(Typed(z, circle), gramIntegrand)));
        Formula haarGramDefinition = MatrixDefinition(
            haarGram, matrixType, index, i, j,
            Call("integral", haar,
                Lambda(Typed(z, circle), gramIntegrand)));

        Formula contactSummand = Seq(
            Grp(Apply(c, i)), Caret, Grp(Star), Sp, Cdot, Sp, Apply(numerator, i));
        Formula contactSum = Seq(
            Sum, Underscore, Grp(i, InMacro, Sp, index), Sp, contactSummand);
        Formula contactDefinition = Seq(
            Typed(contactPolynomial, Arrow(vectorType, polynomial)), Comma, Sp,
            Forall, Sp, Typed(c, vectorType), Comma, Sp,
            Apply(contactPolynomial, c), Sp, Eq, Sp, contactSum);
        Formula letObjects = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            featureDefinition, SemiSpace,
            completionDefinition, SemiSpace,
            gramDefinition, SemiSpace,
            haarGramDefinition, SemiSpace,
            contactDefinition, Close);

        Formula kernel = Seq(
            Call("mulVec", Seq(gram, Sp, Minus, Sp, alpha, Sp, Cdot, Sp, haarGram), c),
            Sp, Eq, Sp, D(0));
        Formula residualMeasure = Seq(
            completion, Sp, Minus, Sp, alpha, Sp, Cdot, Sp, haar);
        Formula zeroSet = new Formula.SetBuilder(
            Seq(Call("eval", Apply(contactPolynomial, c), z), Sp, Eq, Sp, D(0)),
            z, circle);
        Formula conclusion = Seq(
            Call("support", residualMeasure), Sp, Subseteq, Sp, zeroSet);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(n, natural), Comma, Sp,
                Typed(numerator, Arrow(index, polynomial)), Comma),
            Seq(Typed(denominator, polynomial), Comma, Sp,
                Typed(denominatorWitness, denominatorNonzero), Comma),
            Seq(Typed(alpha, nonnegativeReal), Comma, Sp,
                Typed(residual, finiteCircleMeasure), Comma),
            Seq(letObjects, SemiSpace),
            Seq(Forall, Sp, Typed(c, vectorType), Comma, Sp,
                kernel, Sp, Rightarrow),
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
