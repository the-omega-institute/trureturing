using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DelgadoSuerYesilPhiImageBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiImageBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/mazhang2026symmetrizationnegative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pseudo-Frobenius row deletion sends almost symmetric semigroups to symmetric numerical "
            + "sets of Frobenius number 2(F - g + 1) - 1, and at source Frobenius number F at most "
            + "2^(⌊(F+1)/2⌋ - 1) outputs occur.",
        H("The image of row deletion at a fixed source Frobenius number"),
        Blocks(
            Describe.Lean(DescribeId.Create("delgado-suer-yesil-phi-image-bound-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Symmetric output and the image bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let S be an almost symmetric numerical semigroup with genus g and "
                        + "Frobenius number F. The row deletion Φ(S) is a symmetric numerical set "
                        + "of genus F - g + 1 and Frobenius number 2(F - g + 1) - 1 ≤ F. For every "
                        + "F ≥ 1 let S_F be the set of row deletions of the almost symmetric "
                        + "semigroups with Frobenius number F and NS_F the additively closed members "
                        + "of S_F; then 1 ≤ |NS_F| ≤ |S_F| ≤ 2^(⌊(F+1)/2⌋ - 1). The symmetry of the "
                        + "output is Theorem 4.2 of M. Delgado, M. Süer and M. Yeşil; the genus, "
                        + "Frobenius and cardinality statements are Corollary 5 of H. Ma and "
                        + "W. Zhang (version 2).")),
                    Paragraph(Text(
                        "Gaps x with F - x also a gap number 2g - F - 1, because each member "
                        + "a ≤ F has F - a a gap. Every deleted row d, a pseudo-Frobenius gap other "
                        + "than F, has F - d a gap, and almost symmetry 2g = F + |PF(S)| makes the "
                        + "two counts equal, so the deleted rows are exactly these gaps and are "
                        + "closed under x ↦ F - x. A retained row r has F - r a member. If two "
                        + "retained rows r and r' had relabelled values summing to the relabelled "
                        + "Frobenius number, reflecting the deleted rows below r' would make the "
                        + "relabelled value of r equal that of the member s = F - r'; but between "
                        + "r and s, whichever is smaller is not deleted, so fewer deleted rows lie "
                        + "between them than their distance. Hence no pair sums to the output "
                        + "Frobenius number, and as the output has exactly half as many gaps as "
                        + "the integers up to that number, it is symmetric. Every output omits 1 "
                        + "and has odd Frobenius number 2h - 1 with 1 ≤ h ≤ ⌊(F+1)/2⌋; there is one "
                        + "such target for h = 1 and 2^(h-2) for h ≥ 2, giving the bound. The "
                        + "output ℕ₀ ∖ {1} of O_{F+1} is a semigroup."))),
                DescribeRole.Theorem))));
}
