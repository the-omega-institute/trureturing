using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MeijerZeroCount;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpprilepkina2016gammaratio");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gamma quotients and their inverse Mellin zero counts.",
        H("The zero-count comparison"), Blocks(
            Entry("meijer-gamma-quotient", "gammaQuot", "The Gamma quotient",
                "For real parameter vectors a and b of length p, the quotient is the product of Gamma(a(i)+s) divided by the product of Gamma(b(i)+s)."),
            Entry("meijer-inverse-mellin", "meijerG", "The inverse Mellin transform",
                "The function is the inverse Mellin transform of the Gamma quotient along the vertical line of real part one, with normalization one divided by two pi in the real integral."),
            Entry("meijer-control-function", "control", "The control function",
                "The control function at t is the sum of t to the power a(i) minus t to the power b(i). These powers are real powers."),
            Entry("meijer-zero-count-comparison", "claim", "The zero-count comparison",
                "For every positive-length or empty real parameter vector a with nonnegative entries and every real vector b with sum of b(i)-a(i) greater than one, the cardinality of the zero set of the inverse Mellin transform in the unit interval is at most the cardinality of the zero set of the control function there. Cardinalities take values in the extended natural numbers, so infinite zero sets are included. The greater-than-one condition restricts the greater-than-zero parameter range of the conjecture."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
