using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class DerivativeParityReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ContinuousObservables/DerivativeParityReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar reflection and translation symmetries pass to the derivative readout.",
        H("Derivative Parity Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("balanced-field-reflection-is-odd"),
                DeclarationHandle.Create(Prefix + "balanced_field_reflection_odd"),
                H("The balanced field is odd under reflection"),
                StatementSource.FromAuthor(ReflectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every parameter value, a differentiable scalar field that is "
                            + "even in eta has a derivative readout that is odd in eta.")),
                    Paragraph(Text(
                        "The proof uses only the chain rule for eta mapped to -eta and "
                            + "uniqueness of derivatives. The concrete Z_unit family is "
                            + "intentionally left as an external parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-field-periodic"),
                DeclarationHandle.Create(Prefix + "balanced_field_periodic"),
                H("The balanced field keeps the scalar period"),
                StatementSource.FromAuthor(PeriodicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A differentiable scalar field periodic under a translation has a "
                            + "derivative readout with the same translation period.")),
                    Paragraph(Text(
                        "Together the two declarations formalize formulas 765.1--765.3. "
                            + "The source's U^k J^epsilon action, lifted coordinate, connection "
                            + "memory, and arithmetic representation analogy remain outside "
                            + "this self-contained partial closure."))),
                DescribeRole.Theorem))));

    private static Formula ReflectionFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula parameterType = F.Id("S");
        Formula zunitType = Arrow(parameterType, Arrow(reals, reals));
        Formula zunit = F.Id("Zunit");
        Formula s = F.Id("s");
        Formula eta = F.Id("eta");
        Formula u = F.Id("u");

        Formula section = Lambda(u, Apply(zunit, s, u));
        Formula differentiable = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Call("DifferentiableAt", reals, section, eta));
        Formula even = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Equal(Apply(zunit, s, Negate(eta)), Apply(zunit, s, eta)));
        Formula premises = And(differentiable, even);
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Equal(
                Apply(F.Id("balancedField"), zunit, s, Negate(eta)),
                Negate(Apply(F.Id("balancedField"), zunit, s, eta))));

        return Disp(Seq(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("S", F.Id("Type")), Bound("Zunit", zunitType)],
                Implies(premises, conclusion)), Dot));
    }

    private static Formula PeriodicFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula parameterType = F.Id("S");
        Formula zunitType = Arrow(parameterType, Arrow(reals, reals));
        Formula zunit = F.Id("Zunit");
        Formula period = F.Id("period");
        Formula s = F.Id("s");
        Formula eta = F.Id("eta");
        Formula u = F.Id("u");

        Formula section = Lambda(u, Apply(zunit, s, u));
        Formula differentiable = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Call("DifferentiableAt", reals, section, eta));
        Formula periodic = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Equal(Apply(zunit, s, Add(eta, period)), Apply(zunit, s, eta)));
        Formula premises = And(differentiable, periodic);
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", parameterType), Bound("eta", reals)],
            Equal(
                Apply(F.Id("balancedField"), zunit, s, Add(eta, period)),
                Apply(F.Id("balancedField"), zunit, s, eta)));

        return Disp(Seq(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("S", F.Id("Type")), Bound("Zunit", zunitType), Bound("period", reals)],
                Implies(premises, conclusion)), Dot));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Call("lambda", binder, body);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Negate(Formula value) =>
        Seq(Minus, value);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula Implies(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Rightarrow, Sp, Open, right, Close);
}
