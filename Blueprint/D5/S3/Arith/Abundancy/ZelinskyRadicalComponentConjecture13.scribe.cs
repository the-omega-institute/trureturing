using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyRadicalComponentConjecture13Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The radical component condition has relative density one among odd primitive non-deficient integers.",
        H("Zelinsky's Conjecture 13 is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 13"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 13 asserts lim (B intersect C_O)(X)/C_O(X)=0, where C_O consists of "
                    + "the odd primitive non-deficient integers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The relative limit is one, contradicting zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take the empty excluded prime set in the odd squarefree lower bound. Its "
                    + "integers belong to C_O, so C_O(X)>=X^(79/80) eventually. The relative density "
                    + "comparison gives (B intersect C_O)(X)/C_O(X) tending to one. Uniqueness of "
                    + "limits refutes the asserted zero limit."))),
                DescribeRole.Theorem))));
}
