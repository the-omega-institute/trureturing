using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalModularPartnersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-source modular-zero partner bound", H("Original-source modular-zero partner bound"),
        Blocks(
            Paragraph(Text("This local count retains Original.Coordinate, the actual endpoint pencil and the original WordSolution carrier. It combines both dividing orientations with the six-candidate nondividing classification. The source fixed units and physical endpoint units supply nonzero alpha, kappa and the evaluated base linear polynomial after reduction to the prime field. No injectivity of the single linear observation modulo p is assumed.")),
            Paragraph(Text("These conclusions count partners of a fixed nonaligned base in a retained small coordinate chart. They do not count all original six-tuples. The physical multiplicities, excluded strata, available chart conditions and global summation remain separate obligations for the original conjecture.")),
            Describe.Lean(DescribeId.Create("pascadi-actual-all-branches-partner-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalModularPartners.actual_modular_zero_partner_subpower"),
                H("All modular-zero branches have one uniform subpower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive real epsilon there is a positive C, independent of the prime p and the coordinate chart, bounding the actual modular-zero partner cardinality by C times p^epsilon. The base must be an ActualPair, not exactly aligned with q; its evaluated linear polynomial, alpha and kappa must be nonzero. The anchor and E lie in the J1 by J2 coordinate box, with J1,J2 at least one and 8 J1 J2 less than p. If either direction determinant vanishes, the corresponding dividing theorem applies. Otherwise full coordinate reduction is injective on E and the nondividing count is at most six. Increasing the dividing constant by six covers all branches."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-source-partner-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalModularPartners.original_modular_zero_partner_subpower"),
                H("The original retained word solution supplies the required observations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The source modulus c is any nonzero multiple of p, including p cubed. Keep fixed units a1,a2, physical basis vectors R,V, anchor q and an original WordSolution with endpoints a,b in E. Require R's first physical coordinate and the negative second physical coordinate of the anchor to be units; both endpoint first physical coordinates and 1-a1 a2 t times the anchor first physical coordinate are units, where t is the negative anchor second coordinate. The same nonalignment, anchor and endpoint coordinate bounds, J1,J2 at least one and 8 J1 J2 less than p remain explicit.")),
                    Paragraph(Text("Set beta to V's first coordinate divided by R's first coordinate, and alpha to the negative inverse of the product of a1, a2, t and R's first coordinate, in ZMod c. The original word equation gives the actual endpoint product identity. Unit algebra gives units of alpha, kappa and the evaluated base linear polynomial in ZMod c. Mapping along ZMod c to ZMod p preserves these units and the product identity, yielding exactly the premises of the all-branches theorem for the same original modularZeroPartners set."))),
                DescribeRole.Theorem))));
}
