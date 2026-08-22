using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Secrecy;

internal sealed class SubthresholdCoalitionLearnsNothingDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural zero leakage makes every coalition-determined secret function constant, "
            + "while ignorance of the whole secret alone does not imply zero information.",
        H("Subthreshold Coalitions Learn Nothing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("structural-zero-leakage-makes-secret-functions-constant"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "subthreshold_coalition_learns_nothing"),
                H("Structural zero leakage makes secret functions constant"),
                StatementSource.FromAuthor(SubthresholdCoalitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The common readout is the meet of the coalition and secret readouts, "
                            + "and structural zero leakage identifies that meet with the "
                            + "constant concept.")),
                    Paragraph(Text(
                        "Because the target is a function of the secret, its canonical "
                            + "target-image readout factors through the secret. The coalition "
                            + "hypothesis makes it factor through the coalition as well. The "
                            + "meet property therefore makes it factor through the common "
                            + "readout, and hence through the constant concept. Thus every two "
                            + "states have the same target value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("whole-secret-ignorance-does-not-imply-zero-information"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "ignorance_does_not_imply_zero_information"),
                H("Whole-secret ignorance does not imply zero information"),
                StatementSource.FromAuthor(IgnoranceCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a two-bit secret, let the secret readout be the identity and let the "
                        + "coalition see only the first bit. The coalition cannot recover the "
                        + "whole pair because it loses the second bit. Nevertheless, the first "
                        + "bit is a nonconstant function of the secret and factors through the "
                        + "coalition readout. Failure of full-secret recovery is therefore "
                        + "strictly weaker than learning no secret information."))),
                DescribeRole.Lemma))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula CanonicalTarget(Formula target) =>
        Call("canonicalTargetReadout", target);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula SubthresholdCoalitionFormula()
    {
        Formula stateType = F.Id("X");
        Formula coalitionType = F.Id("C");
        Formula secretType = F.Id("S");
        Formula commonType = F.Id("M");
        Formula targetType = F.Id("Y");
        Formula coalition = F.Id("coalition");
        Formula secret = F.Id("secret");
        Formula common = F.Id("common");
        Formula target = F.Id("target");
        Formula secretFunction = F.Id("secretFunction");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula hypotheses = And(
            Call("Nonempty", stateType),
            And(
                Call("IsConceptMeet", coalition, secret, common),
                And(
                    Call(
                        "ConceptEquivalent",
                        common,
                        Call("constantConcept", stateType)),
                    And(
                        Equal(target, Compose(secretFunction, secret)),
                        Refines(CanonicalTarget(target), coalition)))));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", stateType)],
            Equal(Apply(target, x), Apply(target, y)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("C", F.Id("Type")),
                Bound("S", F.Id("Type")),
                Bound("M", F.Id("Type")),
                Bound("Y", F.Id("Type")),
                Bound("coalition", Arrow(stateType, coalitionType)),
                Bound("secret", Arrow(stateType, secretType)),
                Bound("common", Arrow(stateType, commonType)),
                Bound("target", Arrow(stateType, targetType)),
                Bound("secretFunction", Arrow(secretType, targetType)),
            ],
            ImpliesFormula(hypotheses, conclusion)));
    }

    private static Formula IgnoranceCounterexampleFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula pair = Seq(boolean, Sp, Times, Sp, boolean);
        Formula secret = F.Id("id");
        Formula coalition = F.Id("fst");
        Formula target = F.Id("target");
        Formula secretFunction = F.Id("secretFunction");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula nonconstant = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", pair), Bound("y", pair)],
            NotEqual(Apply(target, x), Apply(target, y)));
        Formula partialInformation = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("target", Arrow(pair, boolean)),
                Bound("secretFunction", Arrow(pair, boolean)),
            ],
            And(
                Equal(target, Compose(secretFunction, secret)),
                And(Refines(CanonicalTarget(target), coalition), nonconstant)));

        return Disp(And(
            new Formula.Not(Refines(CanonicalTarget(secret), coalition)),
            partialInformation));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
