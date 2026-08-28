using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalJetDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first derivative layer visible to some normalized toroidal period "
            + "equals the natural vanishing multiplicity of xi.",
        H("Toroidal Jet Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-jet-depth"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalJetDepth."
                        + "toroidal_jet_depth_eq_vanishing_order"),
                H("Toroidal jet depth equals xi multiplicity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The depth is exposed directly as the natural infimum of indices at "
                            + "which some normalized xi-times-twist period has a nonzero "
                            + "iterated derivative.")),
                    Paragraph(Text(
                        "The canonical nonzero endpoint value of xi rules out infinite local "
                            + "order. Mathlib then identifies its natural analytic order with "
                            + "the first nonzero derivative layer.")),
                    Paragraph(Text(
                        "Every twist product has order at least the xi order, while the twist "
                            + "that is nonzero at the observation point realizes equality. "
                            + "Thus the same layer is first visible across the toroidal family."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula naturals = Call("Nat");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula point = F.Id("s");
        Formula twist = F.Id("T");
        Formula index = F.Id("i");
        Formula depth = F.Id("j");
        Formula xi = F.Id("xiReading");
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula periodFunction = Seq(xi, Sp, Times, Sp, Apply(twist, index));

        Formula twistDifferentiable = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Differentiable", complex, Apply(twist, index)));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("i", indexType)],
            NotEqualTo(twistAtPoint, D(0)));
        Formula premises = And(twistDifferentiable, pointwiseNonvanishing);

        Formula visibleAtDepth = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("i", indexType)],
            NotEqualTo(
                Call("iteratedDeriv", depth, periodFunction, point),
                D(0)));
        Formula visibleDepths = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            visibleAtDepth, CloseBrace);
        Formula depthInfimum = Call("sInf", visibleDepths);
        Formula multiplicity = Call("analyticOrderNatAt", xi, point);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("s", complex),
                Bound("T", familyType),
            ],
            Implies(premises, EqualTo(depthInfimum, multiplicity))));
    }
}
