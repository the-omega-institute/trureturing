using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyRadicalComponentConjecture15Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The radical component condition has relative density one among primitive non-deficient integers avoiding finitely many primes.",
        H("Zelinsky's Conjecture 15 is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 15"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every nonempty finite set M of primes, Conjecture 15 asserts lim (B "
                    + "intersect C_M)(X)/C_M(X)=0, where C_M consists of primitive non-deficient "
                    + "integers divisible by no prime in M. The universal quantifier over M and its "
                    + "nonemptiness are retained."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The relative limit is one, contradicting zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every finite prime set M, the odd squarefree lower bound gives "
                    + "C_M(X)>=X^(79/80) eventually. The relative density comparison gives (B "
                    + "intersect C_M)(X)/C_M(X) tending to one for each such M. In particular M={2} "
                    + "contradicts the universally asserted zero limit. No uniform threshold over all "
                    + "M is asserted or needed."))),
                DescribeRole.Theorem))));
}
