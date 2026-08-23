using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Modularity;

internal sealed class InterfaceInsufficiencyDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Componentwise-equal public interfaces cannot verify a differing global target, while "
            + "an explicit factorization through their joint readout supplies a verifier.",
        H("When Modular Interfaces Are Insufficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("modular-interfaces-cannot-verify-global-target"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "modular_interfaces_cannot_verify_global_target"),
                H("Componentwise agreement cannot reveal a global difference"),
                StatementSource.FromAuthor(InterfaceObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose two composite states have the same first-component interface "
                            + "and the same second-component interface, while the global target "
                            + "assigns them different values. Their paired public readouts are "
                            + "therefore identical.")),
                    Paragraph(Text(
                        "Interface blindness forces any verifier to return the same value on "
                            + "those states. A verifier that were correct everywhere would instead "
                            + "return their distinct target values, so no interface-blind verifier "
                            + "can be universally correct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("factorized-target-has-interface-blind-verifier"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "factorized_target_has_interface_blind_verifier"),
                H("A target factoring through the joint interface is verifiable"),
                StatementSource.FromAuthor(FactorizedTargetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the target is a function of the paired component interfaces, compose "
                            + "that factor map with the joint interface and use the composite as "
                            + "the verifier.")),
                    Paragraph(Text(
                        "Equal joint readouts remain equal after applying the factor map, which "
                            + "makes the verifier interface-blind. The factorization identity also "
                            + "makes its output agree with the target on every composite state."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("constant-bool-interfaces-cannot-verify-conjunction"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_bool_interfaces_cannot_verify_conjunction"),
                H("Constant Boolean interfaces cannot verify conjunction"),
                StatementSource.FromAuthor(ConstantBooleanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two constant Unit-valued component interfaces expose the same public "
                            + "pair for every Boolean composite state. In particular, they cannot "
                            + "distinguish (true, true) from (false, false).")),
                    Paragraph(Text(
                        "Boolean conjunction is true on the first state and false on the second. "
                            + "The general componentwise obstruction therefore rules out an "
                            + "interface-blind verifier that computes conjunction everywhere."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(Formula first, Formula second) =>
        Seq(first, Sp, Times, Sp, second);

    private static Formula Pair(Formula first, Formula second) =>
        Call("pair", first, second);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula VerifierExists(
        Formula firstInterface,
        Formula secondInterface,
        Formula target,
        Formula stateType,
        Formula targetType)
    {
        Formula verifier = F.Id("verify");
        Formula state = F.Id("state");
        Formula correctness = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("state"),
            stateType,
            Equal(Apply(verifier, state), Apply(target, state)));

        return new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("verify"),
            Arrow(stateType, targetType),
            And(
                Call("InterfaceBlind", firstInterface, secondInterface, verifier),
                correctness));
    }

    private static Formula InterfaceObstructionFormula()
    {
        Formula firstStateType = F.Id("X1");
        Formula secondStateType = F.Id("X2");
        Formula firstInterfaceType = F.Id("I1");
        Formula secondInterfaceType = F.Id("I2");
        Formula targetType = F.Id("Y");
        Formula firstInterface = F.Id("C1");
        Formula secondInterface = F.Id("C2");
        Formula target = F.Id("T");
        Formula x1 = F.Id("x1");
        Formula y1 = F.Id("y1");
        Formula x2 = F.Id("x2");
        Formula y2 = F.Id("y2");
        Formula stateType = Product(firstStateType, secondStateType);
        Formula hypotheses = And(
            Equal(Apply(firstInterface, x1), Apply(firstInterface, y1)),
            And(
                Equal(Apply(secondInterface, x2), Apply(secondInterface, y2)),
                NotEqual(
                    Apply(target, Pair(x1, x2)),
                    Apply(target, Pair(y1, y2)))));
        Formula conclusion = new Formula.Not(VerifierExists(
            firstInterface,
            secondInterface,
            target,
            stateType,
            targetType));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("X1"), F.Id("Type")),
                new(FormulaIdentifier.Create("X2"), F.Id("Type")),
                new(FormulaIdentifier.Create("I1"), F.Id("Type")),
                new(FormulaIdentifier.Create("I2"), F.Id("Type")),
                new(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new(FormulaIdentifier.Create("C1"), Arrow(firstStateType, firstInterfaceType)),
                new(FormulaIdentifier.Create("C2"), Arrow(secondStateType, secondInterfaceType)),
                new(FormulaIdentifier.Create("T"), Arrow(stateType, targetType)),
                new(FormulaIdentifier.Create("x1"), firstStateType),
                new(FormulaIdentifier.Create("y1"), firstStateType),
                new(FormulaIdentifier.Create("x2"), secondStateType),
                new(FormulaIdentifier.Create("y2"), secondStateType),
            ],
            ImpliesFormula(hypotheses, conclusion)));
    }

    private static Formula FactorizedTargetFormula()
    {
        Formula firstStateType = F.Id("X1");
        Formula secondStateType = F.Id("X2");
        Formula firstInterfaceType = F.Id("I1");
        Formula secondInterfaceType = F.Id("I2");
        Formula targetType = F.Id("Y");
        Formula firstInterface = F.Id("C1");
        Formula secondInterface = F.Id("C2");
        Formula target = F.Id("T");
        Formula factor = F.Id("f");
        Formula stateType = Product(firstStateType, secondStateType);
        Formula interfaceType = Product(firstInterfaceType, secondInterfaceType);
        Formula jointInterface = Call("jointInterface", firstInterface, secondInterface);
        Formula factorization = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("f"),
            Arrow(interfaceType, targetType),
            Equal(target, Seq(factor, Sp, Circ, Sp, jointInterface)));
        Formula conclusion = VerifierExists(
            firstInterface,
            secondInterface,
            target,
            stateType,
            targetType);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("X1"), F.Id("Type")),
                new(FormulaIdentifier.Create("X2"), F.Id("Type")),
                new(FormulaIdentifier.Create("I1"), F.Id("Type")),
                new(FormulaIdentifier.Create("I2"), F.Id("Type")),
                new(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new(FormulaIdentifier.Create("C1"), Arrow(firstStateType, firstInterfaceType)),
                new(FormulaIdentifier.Create("C2"), Arrow(secondStateType, secondInterfaceType)),
                new(FormulaIdentifier.Create("T"), Arrow(stateType, targetType)),
            ],
            ImpliesFormula(factorization, conclusion)));
    }

    private static Formula ConstantBooleanFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula stateType = Product(boolean, boolean);
        Formula constantInterface = Call("constant", boolean, unit);
        Formula verifier = F.Id("verify");
        Formula state = F.Id("state");
        Formula conjunction = Call(
            "boolAnd",
            Call("fst", state),
            Call("snd", state));
        Formula correctness = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("state"),
            stateType,
            Equal(Apply(verifier, state), conjunction));
        Formula candidate = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("verify"),
            Arrow(stateType, boolean),
            And(
                Call("InterfaceBlind", constantInterface, constantInterface, verifier),
                correctness));

        return Disp(new Formula.Not(candidate));
    }
}
