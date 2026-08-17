using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.ErgodicBridge;

internal sealed class TribonacciReproofDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var optimalValuesEqual = Equal(
            Id("tribonacciGridOptimalValue"),
            Id("tribonacciErgodicOptimalValue"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The frozen Tribonacci optimum is reproved by the general Fin-d ergodic bridge.",
            H("Tribonacci General-Bridge Reproof"),
            Blocks(
                Paragraph(Text(
                    "The three frozen gap-geometry laws supply a Fin 3 instance of the general "
                        + "bridge. The instance is separate from the frozen Tribonacci module.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-optimum-follows-from-the-general-bridge"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/TribonacciReproof."
                            + "tribonacci_general_bridge_optimal_value_reproved"),
                    H("The Tribonacci optimum follows from the general bridge"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(optimalValuesEqual)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The old grid and orbit value sets are identified with the general "
                            + "instance sets. General optimality then proves the same equality "
                            + "without invoking the frozen optimality theorem."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ErgodicBridge/General")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ErgodicBridge/Tribonacci")),
            ]));
    }
}
