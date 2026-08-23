using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class MutualRecognitionIsJointRealizabilityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mutual recognition is joint realizability by one admissible world; it neither "
            + "requires equal concepts nor follows from separate realizability.",
        H("Mutual Recognition as Joint Realizability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mutually-recognized-iff-joint-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mutually_recognized_iff_joint_witness"),
                H("Mutual recognition is simultaneous realization"),
                StatementSource.FromAuthor(JointWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A pair of states is mutually recognized exactly when one admissible "
                            + "world produces the first state under the first concept and the "
                            + "second state under the second concept.")),
                    Paragraph(Text(
                        "The two coordinates of a joint readout identify the component "
                            + "realizations. Conversely, component equalities at the same world "
                            + "identify the ordered pair, so the shared witness is the essential "
                            + "content of mutual recognition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mutual-recognition-does-not-require-equal-concepts"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mutual_recognition_does_not_require_equal_concepts"),
                H("Recognizing one pair does not equate the concepts"),
                StatementSource.FromAuthor(UnequalConceptsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the Boolean world space, take the first concept to be constantly "
                            + "false and the second to be the identity. The concepts differ at "
                            + "the true world, yet that world jointly realizes the pair "
                            + "(false, true).")),
                    Paragraph(Text(
                        "Mutual recognition therefore asserts compatibility at one admissible "
                            + "world, not equality of the two readout functions on every world."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "separate-realizability-does-not-imply-mutual-recognition"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "separate_realizability_does_not_imply_mutual_recognition"),
                H("Separate witnesses need not combine into a joint witness"),
                StatementSource.FromAuthor(SeparateWitnessesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let both concepts be the identity on the full Boolean world space. "
                            + "The false state is realized by the false world and the true state "
                            + "is realized by the true world, so both descriptions are separately "
                            + "realizable.")),
                    Paragraph(Text(
                        "No single Boolean world can equal both false and true. Hence the pair "
                            + "(false, true) has no joint witness, showing that separate "
                            + "realizability omits the synchronization required for mutual "
                            + "recognition."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula MutualRecognition(
        Formula admitted,
        Formula firstConcept,
        Formula secondConcept,
        Formula state) =>
        Call("MutuallyRecognized", admitted, firstConcept, secondConcept, state);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula JointWitnessFormula()
    {
        Formula type = F.Id("Type");
        Formula world = F.Id("World");
        Formula firstStateType = F.Id("B1");
        Formula secondStateType = F.Id("B2");
        Formula admitted = F.Id("Adm");
        Formula firstConcept = F.Id("C1");
        Formula secondConcept = F.Id("C2");
        Formula firstState = F.Id("b1");
        Formula secondState = F.Id("b2");
        Formula witness = F.Id("w");
        Formula jointRecognition = MutualRecognition(
            admitted,
            firstConcept,
            secondConcept,
            Pair(firstState, secondState));
        Formula componentRealization = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w"),
            admitted,
            new Formula.Logic(
                Equal(Apply(firstConcept, witness), firstState),
                FormulaLogicOperator.And,
                Equal(Apply(secondConcept, witness), secondState)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("World", type),
                Bound("B1", type),
                Bound("B2", type),
                Bound("Adm", Call("Set", world)),
                Bound("C1", Arrow(world, firstStateType)),
                Bound("C2", Arrow(world, secondStateType)),
                Bound("b1", firstStateType),
                Bound("b2", secondStateType),
            ],
            new Formula.Logic(
                jointRecognition,
                FormulaLogicOperator.Iff,
                componentRealization)));
    }

    private static Formula UnequalConceptsFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula functionType = Arrow(boolean, boolean);
        Formula firstConcept = F.Id("C1");
        Formula secondConcept = F.Id("C2");
        Formula firstState = F.Id("b1");
        Formula secondState = F.Id("b2");
        Formula fullBooleanSet = Call("univ", boolean);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("C1", functionType),
                Bound("C2", functionType),
                Bound("b1", boolean),
                Bound("b2", boolean),
            ],
            new Formula.Logic(
                NotEqual(firstConcept, secondConcept),
                FormulaLogicOperator.And,
                MutualRecognition(
                    fullBooleanSet,
                    firstConcept,
                    secondConcept,
                    Pair(firstState, secondState)))));
    }

    private static Formula SeparateWitnessesFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula admitted = F.Id("Adm");
        Formula firstConcept = F.Id("C1");
        Formula secondConcept = F.Id("C2");
        Formula firstState = F.Id("b1");
        Formula secondState = F.Id("b2");
        Formula witness = F.Id("w");
        Formula firstRealization = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w"),
            admitted,
            Equal(Apply(firstConcept, witness), firstState));
        Formula secondRealization = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w"),
            admitted,
            Equal(Apply(secondConcept, witness), secondState));
        Formula noJointRecognition = new Formula.Not(MutualRecognition(
            admitted,
            firstConcept,
            secondConcept,
            Pair(firstState, secondState)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("Adm", Call("Set", boolean)),
                Bound("C1", Arrow(boolean, boolean)),
                Bound("C2", Arrow(boolean, boolean)),
                Bound("b1", boolean),
                Bound("b2", boolean),
            ],
            new Formula.Logic(
                firstRealization,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    secondRealization,
                    FormulaLogicOperator.And,
                    noJointRecognition))));
    }
}
