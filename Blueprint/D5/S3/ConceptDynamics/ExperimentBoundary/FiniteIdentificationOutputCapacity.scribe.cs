using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentBoundary;

internal sealed class FiniteIdentificationOutputCapacityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity."
            + "finite_identification_output_capacity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separating finite protocol family obeys effective-output capacity bounds.",
        H("Finite Identification Output Capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-identification-output-capacity"),
                DeclarationHandle.Create(Declaration),
                H("Effective outputs bound finite identification capacity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state-class carrier is finite and nonempty, the protocol carrier "
                            + "is a finite type, and each protocol may have its own output type. "
                            + "The canonical jointReadout map is required to be injective.")),
                    Paragraph(Text(
                        "Each effective output count is the cardinality of the actual range of "
                            + "that protocol on the state classes. The displayed formula expands "
                            + "both Lean let-bindings rather than introducing alternate objects.")),
                    Paragraph(Text(
                        "The three public conclusions are the product capacity bound, its "
                            + "base-two logarithmic form, and the uniform-output lower bound for "
                            + "every natural base strictly greater than one."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion"))]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula LtFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula state = F.Id("X");
        Formula protocol = F.Id("P");
        Formula output = F.Id("O");
        Formula readout = F.Id("c");
        Formula index = F.Id("p");
        Formula bound = F.Id("m");
        Formula readoutType = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, protocol), Sp,
            new Formula.TypeArrow(state, Apply(output, index)));
        Formula outputCount = Call(
            "card", Call("range", Apply(readout, index)));
        Formula stateCount = Call("card", state);
        Formula outputProduct = Seq(
            Prod, Underscore, Grp(index, InMacro, Sp, protocol), Sp, outputCount);
        Formula outputLogSum = Seq(
            Sum, Underscore, Grp(index, InMacro, Sp, protocol), Sp,
            new Formula.Log(D(2), outputCount));
        Formula outputBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", protocol)],
            LeqFormula(outputCount, bound));
        Formula uniformBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", naturals)],
            Implies(
                And(LtFormula(D(1), bound), outputBound),
                LeqFormula(
                    Call("natCeil", new Formula.Log(bound, stateCount)),
                    Call("card", protocol))));
        Formula conclusions = And(
            LeqFormula(stateCount, outputProduct),
            And(
                LeqFormula(new Formula.Log(D(2), stateCount), outputLogSum),
                uniformBound));
        Formula assumptions = And(
            Call("Finite", state),
            And(
                Call("Nonempty", state),
                And(
                    Call("Fintype", protocol),
                    Call("Injective", Call("jointReadout", readout)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("P", type),
                Bound("O", new Formula.TypeArrow(protocol, type)),
                Bound("c", readoutType),
            ],
            Implies(assumptions, conclusions)));
    }
}
