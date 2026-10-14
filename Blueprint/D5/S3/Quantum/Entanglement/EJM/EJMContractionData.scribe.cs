using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMContractionDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMContractionData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate exact EJM tail representatives and stored contraction integers.",
        H("Stored contraction proposals require the original-function equality receipts"),
        Blocks(
            Paragraph(Text("Private literal dictionaries store 95 triangle-tail representatives with proposed contraction integers and 332 singleton-tail representatives with their proposed integers. The public functions decode those same dictionaries. This data module contains no theorem asserting that a stored integer is an original coefficient contraction. EJMContractionCertificates must kernel-check the original weighted head sum at every actual representative. Earned contraction symmetries then permit the terminal-bound consumer to transport those equalities; neither external calculation nor a data definition discharges an equality premise.")),
            Node("triangle-tail", "triangleTail", "The actual 95 seven-coordinate triangle-tail proposals",
                "Each index queries the literal tail-code dictionary and decodes seven base-five digits, reduced modulo four. These are the actual representative inputs to the original F1 head-sum checker."),
            Node("triangle-value", "triangleValue", "The actual proposed triangle contraction integer",
                "The original integer dictionary lookup supplies the proposed value at each triangle representative. Its equality to the weighted sum of 64 original F1 head assignments is a separate kernel receipt."),
            Node("singleton-tail", "singletonTail", "The actual 332 eight-coordinate singleton-tail proposals",
                "The singleton tail dictionary is decoded into eight actual Fin 4 outcomes for the original F2 head-sum check."),
            Node("singleton-value", "singletonValue", "The actual proposed singleton contraction integer",
                "The stored integer is a proposal for the sum of four original F2 head values. The additional factor 64 belongs to the separate centered score and is not part of this stored contraction function."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
