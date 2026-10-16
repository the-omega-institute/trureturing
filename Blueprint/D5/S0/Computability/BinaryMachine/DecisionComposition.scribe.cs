using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class DecisionCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial preprocessing before a total verifier.",
        H("Polynomial preprocessing before a total verifier"),
        Blocks(
            Paragraph(Text("A true-halting polynomial transducer first writes its exact output. The unchanged verifier then executes on that output with either Boolean result. Counted same-model simulations prove total polynomial time; determinism gives an equivalence of acceptance on every raw word. This theorem does not infer decision transport from the transducer-only composition interface.")),
            Describe.Lean(
                DescribeId.Create("preprocess"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/DecisionComposition.preprocess"),
                H("preprocess"),
                StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("A true-halting polynomial transducer first writes its exact output. The unchanged verifier then executes on that output with either Boolean result. Counted same-model simulations prove total polynomial time; determinism gives an equivalence of acceptance on every raw word. This theorem does not infer decision transport from the transducer-only composition interface."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/DecisionSimulation"))]));

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
        All("f", Id("WordFunction"), Imp(Call("PolyTime", Id("f")),
        All("M", Id("Machine"), Imp(Call("PolynomialTimeMachine", Id("M")),
            Ex("N", Id("Machine"), And(Call("PolynomialTimeMachine", Id("N")),
                All("x", Id("Word"), Iff(Call("Accepts", Id("N"), Id("x")),
                    Call("Accepts", Id("M"), Call("f", Id("x")))))))))));
}
