using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class NormalTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal left transversals obtained from both total perfect subgroup code cases.",
        H("Total codes supply normal transversals"),
        Blocks(
            Describe.Lean(DescribeId.Create("normal-left-transversal"),
                DeclarationHandle.Create(Prefix + "NLT"), H("The NLT property"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "NLT(H,G) means that some conjugation-invariant subset T is a left "
                    + "transversal of H. The formal definition uses Mathlib Subgroup.IsComplement: "
                    + "multiplication T times H is a bijection onto G. Equivalently T meets each "
                    + "left coset exactly once. No nonsquare or identity-normalization condition "
                    + "is built into NLT."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("total-code-to-nlt"),
                DeclarationHandle.Create(Prefix + "result"), H("Both code branches"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every total perfect subgroup code in a finite group's normal-connection "
                    + "sum graph is NLT. In the singleton-nonsquare case take T=Y. In the "
                    + "two-element case take T=Y without the identity: the square of 1 puts "
                    + "1 in Y, removing it leaves exactly one member in the H-coset and changes "
                    + "no outside-coset intersection. Both choices are normal subsets. "
                    + "This is the total-code part of Proposition 4.1 in the source; it does "
                    + "not establish code inheritance, quotient total-code inheritance, "
                    + "the separate perfect-code route, or the full arbitrary-finite-group "
                    + "abelian equivalence."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
