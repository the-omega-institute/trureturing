using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class BoundedVerifierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total normalization of bounded verifiers.",
        H("Total normalization of bounded verifiers"),
        Blocks(
            Paragraph(Text("The raw word is saved in a disjoint frame before exact paired decoding. Malformed outer words reject. The program checks the target witness bound using the decoded target length; oversized witnesses reject. For a valid bounded pair it restores the identical original raw bytes and executes the original verifier, preserving both decisions. The resulting total polynomial tape machine accepts exactly Good, with no relaxed target certificate bound.")),
            Describe.Lean(
                DescribeId.Create("normalize"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/BoundedVerifier.normalize"),
                H("normalize"),
                StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The raw word is saved in a disjoint frame before exact paired decoding. Malformed outer words reject. The program checks the target witness bound using the decoded target length; oversized witnesses reject. For a valid bounded pair it restores the identical original raw bytes and executes the original verifier, preserving both decisions. The resulting total polynomial tape machine accepts exactly Good, with no relaxed target certificate bound."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/WitnessBudget")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/DecisionSimulation"))]));

    private static Formula All(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, p);
    private static Formula Ex(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, p);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Presentation0() =>
        All("M", Id("Machine"), All("c", Id("Nat"), All("e", Id("Nat"),
        Imp(Call("PolynomialTimeMachine", Id("M")), Ex("N", Id("Machine"),
            And(Call("PolynomialTimeMachine", Id("N")), All("w", Id("Word"),
                Iff(Call("Accepts", Id("N"), Id("w")),
                    Call("Good", Id("M"), Id("c"), Id("e"), Id("w"))))))))));
}
