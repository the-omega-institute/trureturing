using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringTheorem2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/Waring/WaringTheorem2.";
    private static readonly LibraryNoteRef Supplier =
        LibraryNoteRef.Create("D5/L/AdditiveNumberTheory/waringformalization2026lean");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive exponent admits a uniform upper bound on the number of summands.",
        H("The qualitative Hilbert–Waring theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hilbert-waring"),
                DeclarationHandle.Create(Prefix + "waringTheorem"),
                H("Bounded-length sums of natural powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Supplier),
                Blocks(
                    Paragraph(Text(
                        "For each positive exponent, a bound on the summand count works for every natural number. "
                        + "The bases may be zero. "
                        + "The Waring formalization authors proved this Lean theorem using Linnik's method in Jameson's exposition."))
                ),
                DescribeRole.Theorem)
        )));
}
