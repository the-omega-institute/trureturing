using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class DisconnectedRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute successor words realize actual root-separating colorings, with root activity determined by the initial bit and the word entries.",
        H("Actual Realization and Root Activity"),
        Blocks(
            Paragraph(Text("At class j the signed endpoint formulas determine the root incidences of all six original forms. At the reflected class the Form II endpoints are (-(j-1),j). Nonroot role exclusion suffices at the even antipode, where the two fresh signed roles may coincide. The construction imposes no injectivity condition there.")),
            Describe.Lean(DescribeId.Create("even-coloring"), DeclarationHandle.Create(Prefix + "even_native_code_coloring"),
                H("Even actual coloring"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one, every initial bit and every successor word, a Boolean coloring of the actual residues takes values true and false at the two roots and is equal at the endpoints of every selected edge. Radial bands realize each three-step block and the antipodal cap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-coloring"), DeclarationHandle.Create(Prefix + "odd_native_code_coloring"),
                H("Odd actual coloring"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding odd coloring checks the two final paired steps and the singleton edge, as well as every interior block and the starting edge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-root-activity"), DeclarationHandle.Create(Prefix + "even_code_root_activity"),
                H("Even root incidence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every root bit s, the actual root (if s then 1 else -1) is active exactly when b=s or some entry of w equals s. The induction peels three native steps over an arbitrary suffix with an explicit successor state. It includes the empty word and the even cap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-root-activity"), DeclarationHandle.Create(Prefix + "odd_code_root_activity"),
                H("Odd root incidence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one, every initial bit b, every successor word w of length r-1 and every root bit s, the root (if s then 1 else -1) is active in the actual odd coded choice exactly when b=s or some entry of w equals s."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-disconnection"), DeclarationHandle.Create(Prefix + "even_code_disconnected"),
                H("The even excluded word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual even coded choice fails ActiveConnected exactly when w differs from the word constantly equal to its initial bit. Both roots are then active and have different colors. If that word is constant at the initial bit, the opposite root is absent and actual rootedness gives connectivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-disconnection"), DeclarationHandle.Create(Prefix + "odd_code_disconnected"),
                H("The odd excluded word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identical exact exclusion holds for the odd coded choice, using the odd coloring and incidence identities on the original active support."))), DescribeRole.Theorem)), []));
}
