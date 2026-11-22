using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiPrimeCubePairRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed difference package determines at most one prime-square midpoint on each simple unit branch.",
        H("Exact prime-cube word pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-prime-cube-midpoint-equations"),
                DeclarationHandle.Create(Prefix + "primeCube_midpoint_equations"),
                H("Derive the midpoint equations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For an odd prime p and a unit coefficient g, use endpoints x± = z ± pu/2 and "
                    + "slopes ρ± = a ± pt/2. The full slopes y± = ρ±x± and y+ − y− = pv give "
                    + "v = au + tz modulo p². The average of the two exact words gives the central word. "
                    + "Their difference, divided by p, gives its linear coefficient. Putting "
                    + "D = v − au gives t²N = gaQ and aP + NQ = 0, where N and Q are the sum and "
                    + "product of D, and P is the sum of uᵢDⱼDₖ(Dⱼ + Dₖ) over the complementary pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-prime-cube-midpoint-unique"),
                DeclarationHandle.Create(Prefix + "primeCube_midpoint_unique"),
                H("Lift a simple slope and a unit branch"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix g, u and v and the lower residues of a and t. If the lower root of the "
                    + "difference quartic is simple and t and N are nonzero modulo p, then a, t and z "
                    + "are uniquely determined modulo p² among exact pairs. The difference of two "
                    + "candidate slopes has square zero, so the polynomial Taylor identity and the "
                    + "unit derivative determine a. The sum of two lifts of t is a unit because it "
                    + "reduces to 2t. The square equation then determines t, and v − au = tz gives z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-prime-cube-literal-pair-unique"),
                DeclarationHandle.Create(Prefix + "primeCube_literal_pair_unique"),
                H("Determine the integer endpoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Two first triples congruent modulo p² are equal as integer triples when each "
                    + "coordinate varies by less than p². Unit first coordinates allow the exact "
                    + "words to recover both slopes modulo p³. The full slope congruences recover the "
                    + "second triples modulo p³, giving literal equality for coordinate widths less than p³."))),
                DescribeRole.Theorem))));
}
