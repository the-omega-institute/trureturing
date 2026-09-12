using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class CrimGrundyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/CrimGrundyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/basic2026crim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The CRIM Grundy value of (6,6,5,4,3,2,1) is 1, contradicting the printed prediction 3.",
        H("A counterexample to the printed CRIM formula"),
        Blocks(
            Describe.Lean(DescribeId.Create("crim-moves"),
                DeclarationHandle.Create(Prefix + "moves"),
                H("Deleting rows and columns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A position is a decreasing list of positive row lengths. A move removes "
                    + "one row, or conjugates the partition, removes one row, and conjugates "
                    + "back. Conjugation counts the rows reaching each column and omits "
                    + "zero heights. The empty partition has no options. These are the "
                    + "moves of section 3, including the reattachment of the remaining parts."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("crim-grundy"),
                DeclarationHandle.Create(Prefix + "grundy"),
                H("The recursive Grundy value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Grundy value is the least natural number absent from the values "
                    + "of all options. Mathlib finite minima define this least excluded "
                    + "number. Conjugation preserves the total number of cells and every "
                    + "move strictly decreases it, so recursion on cell count defines "
                    + "the value from terminal positions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("crim-printed-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 3 as printed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For positive r,c and 0 ≤ k < min(r,c), the rectair R^k_{r,c} "
                    + "has r-k copies of c followed by c-1 through c-k. For r ≥ 7, "
                    + "printed Conjecture 3 predicts that R^k_{r,r-1} has Grundy value "
                    + "3 when k=r-2 and r is odd, and value 1 otherwise. The claim "
                    + "uses precisely these valid parameters and the CRIM recursion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("crim-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The value at r=7 and k=5"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The partition R^5_{7,6} is (6,6,5,4,3,2,1). A finite certificate "
                    + "contains every descendant, starting with the empty partition. "
                    + "At every position the kernel checks that all options are present, "
                    + "the assigned value is absent from their values, and every smaller "
                    + "natural number occurs. Induction on cell count identifies the "
                    + "certificate values with the recursive Grundy values.")),
                    Paragraph(Text(
                    "The twelve distinct options have value set {0,2,4,5}. Its least "
                    + "excluded value is 1. Since 7 is odd and 5=7-2, the displayed "
                    + "formula instead predicts 3. The theorem negates only the r ≥ 7 "
                    + "formula of printed Conjecture 3. No priority, conclusion about "
                    + "other results, or corrected formula is asserted."))),
                DescribeRole.Theorem))));
}
