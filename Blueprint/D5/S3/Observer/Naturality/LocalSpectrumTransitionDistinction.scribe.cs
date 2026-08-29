using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class LocalSpectrumTransitionDistinctionDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Observer/Naturality/LocalSpectrumTransitionDistinction."
        + "local_spectrum_transition_distinction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal local spectra can hide distinct axes related by an observer transition.",
        H("Local Spectrum Transition Distinction"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-local-spectra-hide-axis-transition"),
            DeclarationHandle.Create(Gid),
            H("Equal local spectra can hide an axis transition"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The local-spectrum readout is invariant under a transitive action on a "
                        + "nontrivial axis space, so it has no left-inverse absolute-axis "
                        + "decoder.")),
                Paragraph(Text(
                    "The declaration exposes distinct axes with equal local spectra together "
                        + "with the group element, observer-world equivalence, and transition "
                        + "computation rule relating those same axes."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula axisType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula spectrumType = F.Id("S");
        Formula type = F.Id("Type");
        Formula observer = F.Id("O");
        Formula transport = F.Id("U");
        Formula spectrum = F.Id("q");
        Formula symmetry = F.Id("g");
        Formula axis = F.Id("a");
        Formula targetAxis = F.Id("b");
        Formula state = F.Id("x");
        Formula decoder = F.Id("d");
        Formula transition = F.Id("T");

        Formula observed = Apply(observer, axis, state);
        Formula covariance = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", group), Bound("a", axisType), Bound("x", stateType)],
            Equal(
                Apply(observer, Smul(symmetry, axis), Smul(symmetry, state)),
                Apply(Apply(transport, symmetry), observed)));
        Formula spectrumInvariant = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", group), Bound("a", axisType)],
            Equal(Apply(spectrum, Smul(symmetry, axis)), Apply(spectrum, axis)));
        Formula noDecoder = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("d", Arrow(spectrumType, axisType))],
            Call("LeftInverse", decoder, spectrum)));
        Formula worldA = Call("range", Apply(observer, axis));
        Formula worldB = Call("range", Apply(observer, targetAxis));
        Formula transitionRule = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType)],
            Equal(
                Apply(transition, observed),
                Apply(Apply(transport, symmetry), observed)));
        Formula transitionWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("a", axisType),
                Bound("b", axisType),
                Bound("g", group),
                Bound("T", Call("Equiv", worldA, worldB)),
            ],
            And(
                NotEqual(axis, targetAxis),
                And(
                    Equal(Apply(spectrum, axis), Apply(spectrum, targetAxis)),
                    And(
                        Equal(Smul(symmetry, axis), targetAxis),
                        transitionRule))));

        Formula assumptions = And(
            Call("Group", group),
            And(
                Call("MulAction", group, axisType),
                And(
                    Call("MulAction", group, stateType),
                    And(
                        Call("IsPretransitive", group, axisType),
                        Call("Nontrivial", axisType)))));
        Formula body = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("O", Arrow(axisType, Arrow(stateType, outputType))),
                Bound("U", Arrow(group, Call("Equiv", outputType, outputType))),
                Bound("q", Arrow(axisType, spectrumType)),
            ],
            new Formula.Logic(
                And(covariance, spectrumInvariant),
                FormulaLogicOperator.Implies,
                And(noDecoder, transitionWitness)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("G", type),
                Bound("A", type),
                Bound("X", type),
                Bound("Y", type),
                Bound("S", type),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, body)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Smul(Formula action, Formula value) =>
        Call("smul", action, value);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
