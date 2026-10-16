using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class NPPreimageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NP preimages with exact target witness bounds.",
        H("NP preimages with exact target witness bounds"),
        Blocks(
            Paragraph(Text("A target verifier is normalized to enforce its original witness bound before its original decision. PairPreimage transforms only the instance; DecisionComposition preserves the complete normalized decision. The physical output bound for the reduction supplies a polynomial source witness envelope. Soundness uses the target bound checked internally, so an oversized target witness cannot become valid merely because the source envelope is larger. coNP is defined by complements of NP languages, and DP by intersections of an NP language and a coNP language.")),
            Describe.Lean(
                DescribeId.Create("innp-preimage"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/NPPreimage.inNP_preimage"),
                H("inNP_preimage"),
                StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("A target verifier is normalized to enforce its original witness bound before its original decision. PairPreimage transforms only the instance; DecisionComposition preserves the complete normalized decision. The physical output bound for the reduction supplies a polynomial source witness envelope. Soundness uses the target bound checked internally, so an oversized target witness cannot become valid merely because the source envelope is larger. coNP is defined by complements of NP languages, and DP by intersections of an NP language and a coNP language."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PairPreimage")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/BoundedVerifier")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/DecisionComposition"))]));

    private static Formula All(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Presentation0() =>
        All("A", Id("Language"), All("f", Id("WordFunction"),
        Imp(Call("InNP", Id("A")), Imp(Call("PolyTime", Id("f")),
            Call("InNP", Call("preimage", Id("A"), Id("f")))))));
}
