using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class MultilayerIdentityInsufficiencyDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete two-layer cone loses its upper bit, and noninjective projections neither "
            + "admit left inverses nor determine a unique fiber-constant assignment.",
        H("Multilayer Identity Insufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-layer-cone-loses-high-information"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "two_layer_cone_nonempty_and_loses_high_information"),
                H("The two-layer cone loses its upper bit"),
                StatementSource.FromAuthor(TwoLayerConeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The concrete system has a one-point lower layer and a Boolean upper "
                            + "layer. Each Boolean value determines a compatible subject, so the "
                            + "space of compatible families is inhabited.")),
                    Paragraph(Text(
                        "The subjects determined by false and true have the same lower component "
                            + "because the downward projection forgets the bit, while their upper "
                            + "components remain distinct. Thus lower-layer agreement does not "
                            + "recover the higher-layer state."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("noninjective-layer-cannot-recover"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "noninjective_layer_cannot_recover"),
                H("A noninjective layer cannot recover or choose uniquely"),
                StatementSource.FromAuthor(NoninjectiveRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A left inverse would force the layer projection to be injective. Hence "
                            + "a noninjective projection admits no recovery map that reconstructs "
                            + "every higher-layer state.")),
                    Paragraph(Text(
                        "When the normative codomain contains two distinct values, the two "
                            + "constant assignments to those values are both constant on every "
                            + "projection fiber. They are distinct legal assignments, so fiber "
                            + "compatibility alone does not select a unique high-level choice."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Component(Formula subject, byte layer) =>
        new Formula.Subscript(subject, D(layer));

    private static Formula TwoLayerConeFormula()
    {
        Formula family = Call(
            "CompatibleFamily",
            F.Id("twoLayerState"),
            F.Id("twoLayerProjection"));
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", family), Bound("y", family)],
            And(
                Equal(Component(left, 0), Component(right, 0)),
                NotEqual(Component(left, 1), Component(right, 1))));

        return Disp(And(Call("Nonempty", family), witness));
    }

    private static Formula NoninjectiveRecoveryFormula()
    {
        Formula highLayer = F.Id("Sj");
        Formula lowLayer = F.Id("Si");
        Formula normative = F.Id("Norm");
        Formula projection = F.Id("p");
        Formula firstValue = F.Id("n1");
        Formula secondValue = F.Id("n2");
        Formula recovery = F.Id("r");
        Formula firstAssignment = F.Id("q1");
        Formula secondAssignment = F.Id("q2");

        Formula assumptions = And(
            new Formula.Not(Call("Injective", projection)),
            NotEqual(firstValue, secondValue));
        Formula noLeftInverse = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("r", Arrow(lowLayer, highLayer))],
            Call("LeftInverse", recovery, projection)));
        Formula distinctAssignments = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q1", Arrow(highLayer, normative)),
                Bound("q2", Arrow(highLayer, normative)),
            ],
            And(
                Call("FiberConstant", projection, firstAssignment),
                And(
                    Call("FiberConstant", projection, secondAssignment),
                    NotEqual(firstAssignment, secondAssignment))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Sj", F.Id("Type")),
                Bound("Si", F.Id("Type")),
                Bound("Norm", F.Id("Type")),
                Bound("p", Arrow(highLayer, lowLayer)),
                Bound("n1", normative),
                Bound("n2", normative),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                And(noLeftInverse, distinctAssignments))));
    }
}
