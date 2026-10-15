using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMPartialBoundDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Untrusted original local partial-bound data with an explicit total decoder.",
        H("Every actual row field remains available to the checker"),
        Blocks(
            Paragraph(Text("The local orbit DAGs contain 41294 triangle rows in ten-coordinate order and 8689 singleton rows in nine-coordinate order. RawRow records either a terminal hash and integer bound or a branch hash, bound, split coordinate, packed children and packed actions. RawTree stores packed natural-number payloads. Each row occupies 164 bits: a 24-bit base-five hash, 32-bit biased signed bound, 8-bit coordinate, four 16-bit children and four 9-bit actions; 128 rows occupy each stored natural number. These definitions supply proposed rows, not mathematical validity. The complete actual structural checks, exact local actions, terminal inequalities and contraction values must be earned by their kernel consumers before any local acceptance theorem follows.")),
            Node("raw-lookup", "get", "Packed natural-number dictionary lookup",
                "The binary interpreter returns a matching payload, follows the query ordering to a child, and returns zero on an empty lookup. No producer assertion participates in this interpretation."),
            Node("unpack", "unpack", "Decode the original 164-bit row fields",
                "The decoder reads the fixed bit fields, subtracts 2147483648 from the signed-bound field, and uses coordinate equal to the supplied dimension as the terminal tag. Other coordinates give a branch retaining all four children and actions."),
            Node("read", "read", "Select one original row from a packed payload",
                "The row index selects a stored natural via division by 128 and selects its 164-bit field via the remainder. This total decoding function is data access and does not prove its decoded row passes a check."),
            Node("scale", "scale", "The exact recorded-bound scale",
                "The integer scale is 6987435. The actual row interpreter multiplies each recorded lower bound by this same scale; all later inequalities concern the resulting integer value."),
            Node("digit", "digit", "Base-five coordinate decoding",
                "A hash coordinate is its base-five digit, using natural-number division and remainder. Outcomes zero through three are known values and digit four represents unknown in a partial event."),
            Node("partial-event", "partialEvent", "Decode the actual partial assignment",
                "Digits below four produce the corresponding known Fin 4 outcome. Other digits produce none, preserving the original partial-assignment semantics used by every compatibility and transport check."),
            Node("complete-event", "event", "Decode a total four-valued event",
                "Each base-five digit is reduced modulo four to produce a total Fin 4 outcome. Whether a decoded complete event matches its stored partial assignment is a separate checker obligation."),
            Node("outcomes", "outcome", "Twenty-four literal common-outcome maps",
                "The table defines the actual common outcome functions used by local actions. Their bijectivity and compatibility/score transport laws are proved in the separate local transport consumer; the table alone supplies no such theorem."),
            Node("action", "action", "Decode a local coordinate/outcome action tag",
                "The code gives a Fin 12 coordinate index and Fin 24 outcome index using division by 24 and the indicated modular reductions. LocalSym is the corresponding pair type."),
            Node("row", "row", "Interpret every original raw row as a complete or split rule",
                "The interpreter scales the bound, decodes the partial event, and constructs the actual complete event or all four split children/actions. Coordinate and child indices are reduced into their finite domains. These totality conversions do not replace checks of exact assignments, earlier-child order, lower-bound direction or terminal score inequalities."),
            Node("triangle-tree", "triangleTree", "The complete packed triangle data tree",
                "This tree assembles the original packed payloads for all triangle rows. It is a concrete input to the decoder, without an assumed checkStructure or checkRow acceptance theorem."),
            Node("triangle-rows", "triangleRows", "The actual 41294 triangle rows",
                "Each row is read from the complete triangle tree and interpreted with dimension ten and the actual row count. Every structural and numerical consumer uses this same row function."),
            Node("singleton-tree", "singletonTree", "The complete packed singleton data tree",
                "This is the corresponding original singleton payload tree. Storing a claimed lower bound does not prove that bound at a terminal event or every compatible completion."),
            Node("singleton-rows", "singletonRows", "The actual 8689 singleton rows",
                "The singleton row function uses the original tree, dimension nine and actual row count. Full row acceptance requires all actual premises to be kernel-checked in the downstream certificate."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
