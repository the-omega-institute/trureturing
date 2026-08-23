using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reporting;

internal sealed class PhenomenalSupervenienceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Phenomenal factorization through a selected joint public readout is exactly the "
            + "absence of a zombie witness, with Boolean choices realizing both outcomes.",
        H("Phenomenal Supervenience and Zombie Witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phenomenal-supervenience-exactly-excludes-zombie-witnesses"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Reporting/PhenomenalSupervenience."
                        + "supervenience_xor_zombie_witness"),
                H("Phenomenal supervenience is equivalent to having no zombie witness"),
                StatementSource.FromAuthor(SupervenienceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On any inhabited state space, a phenomenal readout factors through "
                            + "the joint value of two selected public readouts exactly when it "
                            + "is constant on every joint-public fiber. Equivalently, no two "
                            + "publicly indistinguishable states differ phenomenally.")),
                    Paragraph(Text(
                        "For the first Boolean instance, both public coordinates are constantly "
                            + "false. The states false and true therefore have the same joint "
                            + "public value, while the identity phenomenal readout distinguishes "
                            + "them, producing a zombie witness.")),
                    Paragraph(Text(
                        "For the second Boolean instance, the first public coordinate is the "
                            + "identity. Equality of joint public values then forces equality of "
                            + "the states, so the identity phenomenal readout cannot differ. "
                            + "Changing only the selected public concept removes the witness."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TypeUniverse() => F.Id("Type");

    private static Formula SupervenienceFormula()
    {
        Formula stateType = F.Id("X");
        Formula phenomenalType = F.Id("Phenomenal");
        Formula publicLeftType = F.Id("PublicLeft");
        Formula publicRightType = F.Id("PublicRight");
        Formula phenomenal = F.Id("p");
        Formula publicLeft = F.Id("qL");
        Formula publicRight = F.Id("qR");
        Formula publicJoin = Call("conceptJoin", publicLeft, publicRight);
        Formula criterion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("Phenomenal", TypeUniverse()),
                Bound("PublicLeft", TypeUniverse()),
                Bound("PublicRight", TypeUniverse()),
                Bound("p", Arrow(stateType, phenomenalType)),
                Bound("qL", Arrow(stateType, publicLeftType)),
                Bound("qR", Arrow(stateType, publicRightType)),
            ],
            ImpliesFormula(
                Call("Nonempty", stateType),
                IffFormula(
                    Call("Refines", phenomenal, publicJoin),
                    new Formula.Not(Call("ZombieWitness", phenomenal, publicJoin)))));

        Formula boolean = F.Id("Bool");
        Formula identity = Call("identity", boolean);
        Formula constantFalse = Call("constant", F.Id("false"));
        Formula constantPublicJoin = Call("conceptJoin", constantFalse, constantFalse);
        Formula separatingPublicJoin = Call("conceptJoin", identity, constantFalse);
        Formula witnessExists = Call("ZombieWitness", identity, constantPublicJoin);
        Formula witnessExcluded = new Formula.Not(
            Call("ZombieWitness", identity, separatingPublicJoin));

        return Disp(And(criterion, And(witnessExists, witnessExcluded)));
    }
}
