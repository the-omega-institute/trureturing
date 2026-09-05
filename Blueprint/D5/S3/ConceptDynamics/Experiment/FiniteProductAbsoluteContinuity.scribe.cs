using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FiniteProductAbsoluteContinuityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nondegenerate Boolean marginals have positive atoms, and their finite "
            + "coordinatewise product dominates every measure on Boolean transcripts.",
        H("Finite Product Absolute Continuity"),
        Blocks(
            Paragraph(Text(
                "The law marginal p is the Boolean coordinate law with success probability p. "
                    + "It is defined in the frozen module "
                    + "InfiniteIdentificationFiniteInexactness and is used here through an "
                    + "import.")),
            Paragraph(Text(
                "When every reference coordinate law is nondegenerate, its finite product "
                    + "charges every singleton transcript. A set that is null for the reference "
                    + "product must therefore be empty. Consequently any measure at all on the "
                    + "transcript space is absolutely continuous with respect to that product; "
                    + "the dominated measure's only role is to vanish on the empty set.")),
            Paragraph(Text(
                "An earlier draft stated only the identically distributed case and asserted in "
                    + "its own prose that no strengthening was available. A review seat showed "
                    + "that claim was false: the same proof permits an arbitrary dominated "
                    + "measure and a coordinatewise family of reference laws. The theorem "
                    + "absolutelyContinuous_pi_marginal is the correction. The identically "
                    + "distributed form remains as a corollary because that is the shape the "
                    + "repository re-derives.")),
            Paragraph(Text(
                "ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation "
                    + "and ConceptDynamics/ExperimentDesign/"
                    + "FinitePrefixInfiniteCompletionSeparation each carry a private copy of "
                    + "the identically distributed theorem and a private copy of the two-bound "
                    + "singleton-positivity theorem: four private declarations in total. Both "
                    + "modules are frozen, so they cannot import this module, and this change "
                    + "removes none of the four declarations.")),
            Paragraph(Text(
                "This module has zero consumers today. The two single-outcome lemmas and the "
                    + "general domination theorem are strictly stronger than anything the "
                    + "repository currently states; the combined singleton lemma and the "
                    + "identically distributed corollary are API.")),
            Paragraph(Text(
                "No claim of novel mathematics is made. The atomic proofs evaluate one Boolean "
                    + "outcome, the combined result is a case split, the general theorem applies "
                    + "singleton positivity coordinatewise, and the corollary is a one-step "
                    + "instantiation.")),
            Paragraph(Text(
                "Pinned Mathlib has Measure.AbsolutelyContinuous.prod for binary products and "
                    + "Measure.pi_singleton for a singleton of a finite indexed product; the "
                    + "latter is used in the proof. The search found no upstream statement of "
                    + "this domination. That is a report of the search result, not a claim that "
                    + "no upstream form can exist.")),
            Describe.Lean(
                DescribeId.Create("marginal-true-pos"),
                DeclarationHandle.Create(DeclarationPrefix + "marginal_true_pos"),
                H("Positive success probability gives positive mass to true"),
                StatementSource.FromAuthor(MarginalTruePositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a point p of the unit interval, the sole hypothesis is that its real "
                        + "value is positive. Then marginal p assigns positive mass to true. No "
                        + "upper bound on p is assumed or needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("marginal-false-pos"),
                DeclarationHandle.Create(DeclarationPrefix + "marginal_false_pos"),
                H("Success probability below one gives positive mass to false"),
                StatementSource.FromAuthor(MarginalFalsePositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a point p of the unit interval, the sole hypothesis is that its real "
                        + "value is below one. Then marginal p assigns positive mass to false. "
                        + "No lower bound on p is assumed or needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("marginal-singleton-pos"),
                DeclarationHandle.Create(DeclarationPrefix + "marginal_singleton_pos"),
                H("Every outcome of a nondegenerate Boolean marginal has positive mass"),
                StatementSource.FromAuthor(MarginalSingletonPositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the real value of p is strictly between zero and one, every Boolean "
                        + "outcome has positive singleton mass under marginal p. Both bounds are "
                        + "present because the quantified outcome may be either false or true."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("absolutely-continuous-pi-marginal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "absolutelyContinuous_pi_marginal"),
                H("A finite nondegenerate marginal product dominates every measure"),
                StatementSource.FromAuthor(AbsolutelyContinuousPiMarginalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Index be finite, let mu be an arbitrary measure on Boolean transcripts, "
                        + "and let q assign a unit-interval point to every coordinate. There is no "
                        + "hypothesis on mu. If every real value q i is positive and below one, "
                        + "then mu is absolutely continuous with respect to the product whose "
                        + "ith coordinate law is marginal of q i."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-product-absolutely-continuous"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_product_absolutelyContinuous"),
                H("One finite Boolean product law is dominated by a nondegenerate one"),
                StatementSource.FromAuthor(FiniteProductAbsolutelyContinuousFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite index type and unit-interval points p and q, only the two "
                        + "strict bounds on the real value of q are assumed. The product of "
                        + "copies of marginal p is absolutely continuous with respect to the "
                        + "product of copies of marginal q; no bound on p is required."))),
                DescribeRole.Theorem))));

    private static Formula MarginalTruePositiveFormula()
    {
        Formula point = F.Id("p");
        Formula hypothesis = StrictlyLess(Num(0), RealValue(point));
        Formula conclusion = StrictlyLess(
            Num(0),
            SingletonMass(point, F.Id("true")));

        return Disp(Seq(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [PointVariable()],
                new Formula.Logic(
                    hypothesis,
                    FormulaLogicOperator.Implies,
                    conclusion)),
            Dot));
    }

    private static Formula MarginalFalsePositiveFormula()
    {
        Formula point = F.Id("p");
        Formula hypothesis = StrictlyLess(RealValue(point), Num(1));
        Formula conclusion = StrictlyLess(
            Num(0),
            SingletonMass(point, F.Id("false")));

        return Disp(Seq(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [PointVariable()],
                new Formula.Logic(
                    hypothesis,
                    FormulaLogicOperator.Implies,
                    conclusion)),
            Dot));
    }

    private static Formula MarginalSingletonPositiveFormula()
    {
        Formula point = F.Id("p");
        Formula outcome = F.Id("outcome");
        Formula pointValue = RealValue(point);
        Formula bounds = new Formula.Logic(
            StrictlyLess(Num(0), pointValue),
            FormulaLogicOperator.And,
            StrictlyLess(pointValue, Num(1)));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("outcome"),
                    F.Id("Bool")),
            ],
            StrictlyLess(Num(0), SingletonMass(point, outcome)));

        return Disp(Seq(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [PointVariable()],
                new Formula.Logic(
                    bounds,
                    FormulaLogicOperator.Implies,
                    conclusion)),
            Dot));
    }

    private static Formula AbsolutelyContinuousPiMarginalFormula()
    {
        Formula indexType = F.Id("Index");
        Formula measure = F.Id("mu");
        Formula family = F.Id("q");
        Formula transcriptType = Arrow(indexType, F.Id("Bool"));
        Formula familyType = Arrow(indexType, F.Id("unitInterval"));
        Formula bounds = CoordinateBounds(indexType, family);
        Formula referenceProduct = ProductMeasure(
            indexType,
            index => Apply(family, index));
        Formula conclusion = Apply(
            F.Id("AbsolutelyContinuous"),
            measure,
            referenceProduct);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), indexType)), Comma),
            Seq(
                Forall, Sp, measure, Colon, Sp, MeasureType(transcriptType), Comma, Sp,
                family, Colon, Sp, familyType, Comma),
            Seq(bounds, Sp, Rightarrow),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula FiniteProductAbsolutelyContinuousFormula()
    {
        Formula indexType = F.Id("Index");
        Formula point = F.Id("p");
        Formula reference = F.Id("q");
        Formula referenceValue = RealValue(reference);
        Formula bounds = new Formula.Logic(
            StrictlyLess(Num(0), referenceValue),
            FormulaLogicOperator.And,
            StrictlyLess(referenceValue, Num(1)));
        Formula conclusion = Apply(
            F.Id("AbsolutelyContinuous"),
            ConstantProductMeasure(indexType, point),
            ConstantProductMeasure(indexType, reference));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), indexType)), Comma),
            Seq(
                Forall, Sp, point, Comma, Sp, reference, Colon, Sp,
                F.Id("unitInterval"), Comma),
            Seq(bounds, Sp, Rightarrow),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula CoordinateBounds(Formula indexType, Formula family)
    {
        Formula index = F.Id("i");
        Formula coordinateValue = RealValue(Apply(family, index));
        Formula lower = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("i"),
                    indexType),
            ],
            StrictlyLess(Num(0), coordinateValue));
        Formula upper = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("i"),
                    indexType),
            ],
            StrictlyLess(coordinateValue, Num(1)));

        return new Formula.Logic(lower, FormulaLogicOperator.And, upper);
    }

    private static Formula ProductMeasure(
        Formula indexType,
        Func<Formula, Formula> coordinate)
    {
        Formula index = F.Id("i");
        Formula family = Seq(
            index, Colon, Sp, indexType, Sp, Mapsto, Sp,
            Marginal(coordinate(index)));

        return Apply(F.Id("MeasurePi"), family);
    }

    private static Formula ConstantProductMeasure(Formula indexType, Formula point) =>
        ProductMeasure(indexType, _ => point);

    private static Formula SingletonMass(Formula point, Formula outcome) =>
        Apply(Marginal(point), new Formula.SetLiteral([outcome]));

    private static Formula Marginal(Formula point) =>
        Apply(F.Id("marginal"), point);

    private static Formula RealValue(Formula point) =>
        Seq(Open, point, Colon, Sp, Mathbb, Grp(F.Id("R")), Close);

    private static Formula MeasureType(Formula carrier) =>
        Apply(F.Id("Measure"), carrier);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula StrictlyLess(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Typeclass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula.BoundVariable PointVariable() =>
        new Formula.BoundVariable(
            FormulaIdentifier.Create("p"),
            F.Id("unitInterval"));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
