using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringTheorem2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/Waring/WaringTheorem2.";
    private static readonly LibraryNoteRef Supplier =
        LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean");

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
                        + "Hilbert first proved the qualitative theorem. "
                        + "The Waring formalization authors proved the Lean theorem using Linnik's method as presented in Tim Jameson's notes."))
                ),
                DescribeRole.Theorem)
        )));
}
