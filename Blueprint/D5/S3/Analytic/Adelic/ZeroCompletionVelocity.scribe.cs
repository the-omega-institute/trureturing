using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ZeroCompletionVelocityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A simple zero thread moves by the ratio of completion and spatial derivatives.",
        H("Zero Completion Velocity"),
        Blocks(Describe.Lean(
            DescribeId.Create("zero-completion-velocity"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Adelic/ZeroCompletionVelocity."
                    + "zero_completion_velocity"),
            H("The two partial derivatives determine zero motion"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The bivariate Frechet derivative is displayed on the completion and "
                        + "spatial coordinate projections, so dCompletion and dSpatial are "
                        + "the two distinct partial derivatives of the same analytic object.")),
                Paragraph(Text(
                    "The named thread rho is differentiable with velocity v and remains in "
                        + "the zero locus at every completion parameter. Composing the joint "
                        + "derivative with that thread therefore gives zero total derivative.")),
                Paragraph(Text(
                    "Since the spatial coefficient is nonzero, cancellation solves the chain "
                        + "rule identity for v and yields the displayed quotient."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula pair = Call("Prod", real, complex);
        Formula function = F.Id("F");
        Formula thread = F.Id("rho");
        Formula parameter = F.Id("tau");
        Formula dCompletion = F.Id("dCompletion");
        Formula dSpatial = F.Id("dSpatial");
        Formula velocity = F.Id("v");
        Formula point = F.Id("p");
        Formula variable = F.Id("u");
        Formula functionType = Arrow(real, Arrow(complex, complex));
        Formula threadType = Arrow(real, complex);
        Formula pointFirst = Call("fst", point);
        Formula pointSecond = Call("snd", point);
        Formula uncurriedFunction = Lambda(
            point,
            Apply(Apply(function, pointFirst), pointSecond));
        Formula derivativeMap = Seq(
            Call("smulRight", Call("fstCLM", pair, real), dCompletion),
            Sp, Plus, Sp,
            Call("comp", Call("mulCLM", dSpatial), Call("sndCLM", pair, complex)));
        Formula pointOnThread = Call("pair", parameter, Apply(thread, parameter));
        Formula jointDerivative = Call(
            "HasFDerivAt",
            uncurriedFunction,
            derivativeMap,
            pointOnThread);
        Formula threadDerivative = Call(
            "HasDerivAt",
            thread,
            velocity,
            parameter);
        Formula zeroThread = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", real)],
            EqualTo(Apply(Apply(function, variable), Apply(thread, variable)), D(0)));
        Formula premises = And(
            jointDerivative,
            And(threadDerivative, And(zeroThread, NotEqualTo(dSpatial, D(0)))));
        Formula quotient = Seq(
            Minus,
            new Formula.Fraction(dCompletion, dSpatial));
        Formula conclusion = EqualTo(velocity, quotient);

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("F", functionType),
                Bound("rho", threadType),
                Bound("tau", real),
                Bound("dCompletion", complex),
                Bound("dSpatial", complex),
                Bound("v", complex),
            ],
            Implies(premises, conclusion));
    }
}
