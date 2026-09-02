using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Toroidal;

internal sealed class ProjectiveJetScaleInvarianceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance."
            + "projective_toroidal_jet_scale_invariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero constant rescaling preserves the normalized projective "
            + "toroidal jet fingerprint.",
        H("Projective Toroidal Jet Scale Invariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("projective-toroidal-jet-scale-invariance"),
            DeclarationHandle.Create(Declaration),
            H("Common nonzero scale leaves the fingerprint unchanged"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The fingerprint records the supplied anchor order m and the next r "
                        + "iterated derivatives divided by the nonzero derivative at m. "
                        + "This invariance theorem is the named property that earns the "
                        + "fingerprint and normalized-jet definitions.")),
                Paragraph(Text(
                    "Multiplication by a nonzero constant preserves every earlier zero and "
                        + "the nonzero anchor. The same constant then cancels from every "
                        + "normalized derivative ratio.")),
                Paragraph(Text(
                    "The anchor order is supplied by the displayed hypotheses. "
                        + "ToroidalJetDepth may produce such an order for a later consumer, "
                        + "but it is not a dependency here. No zeta, Riemann-hypothesis, or "
                        + "C-1 chart statement is asserted."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(
        Formula binder, Formula domain, Formula body) =>
        Seq(Open, binder, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula naturals = Call("Nat");
        Formula period = F.Id("period");
        Formula point = F.Id("s");
        Formula scale = F.Id("c");
        Formula order = F.Id("m");
        Formula length = F.Id("r");
        Formula index = F.Id("j");
        Formula variable = F.Id("z");
        Formula zero = D(0);
        Formula functionType = Arrow(complex, complex);
        Formula scaledPeriod = Lambda(
            variable,
            complex,
            Seq(scale, Sp, Times, Sp, Apply(period, variable)));

        Formula scaleNonzero = NotEqualTo(scale, zero);
        Formula earlierVanish = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", naturals)],
            Implies(
                LessThan(index, order),
                EqualTo(Call("iteratedDeriv", index, period, point), zero)));
        Formula anchorNonzero = NotEqualTo(
            Call("iteratedDeriv", order, period, point), zero);
        Formula hypotheses = And(
            scaleNonzero,
            And(earlierVanish, anchorNonzero));

        Formula originalJet = Call(
            "projectiveToroidalJet", period, point, order, length);
        Formula scaledJet = Call(
            "projectiveToroidalJet", scaledPeriod, point, order, length);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("period", functionType),
                Bound("s", complex),
                Bound("c", complex),
                Bound("m", naturals),
                Bound("r", naturals),
            ],
            Implies(hypotheses, EqualTo(originalJet, scaledJet))));
    }
}
