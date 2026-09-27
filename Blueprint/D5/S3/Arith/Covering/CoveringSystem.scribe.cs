using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class CoveringSystemDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/CoveringSystem.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of congruence classes that covers the integers has reciprocal moduli "
            + "summing to at least one.",
        H("Covering systems and the reciprocal bound"),
        Blocks(
            Paragraph(Text(
                "A covering system is a finite family of congruence classes whose union is all of "
                    + "the integers. Two further conditions carry the hypotheses under which "
                    + "covering systems are usually studied, distinctness of the moduli and "
                    + "oddness of every modulus; they are recorded here as the vocabulary in which "
                    + "those questions are stated, and the bound below does not assume them.")),
            Describe.Lean(
                DescribeId.Create("covering-system-definition"),
                DeclarationHandle.Create(Prefix + "IsCoveringSystem"),
                H("Covering systems"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite set of pairs of naturals is a covering system when every modulus, "
                        + "the second entry, is at least one, and every integer is congruent to "
                        + "the first entry modulo the second for at least one pair. Coverage is "
                        + "stated over the integers, so negative integers are included, and the "
                        + "residue is not required to be reduced modulo the modulus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distinct-moduli"),
                DeclarationHandle.Create(Prefix + "IsDistinct"),
                H("Distinct moduli"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every modulus is at least two and distinct members of the system carry "
                        + "distinct moduli."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-moduli"),
                DeclarationHandle.Create(Prefix + "AllOdd"),
                H("Odd moduli"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every modulus of the system is odd."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reciprocal-modulus-bound"),
                DeclarationHandle.Create(Prefix + "sum_reciprocal_moduli_ge_one"),
                H("The reciprocal bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a covering system the sum of the reciprocals of the moduli is at least "
                        + "one. Take a common period, namely a multiple of every modulus, and "
                        + "count the naturals below it. The class of one member meets that range "
                        + "in exactly the period divided by its modulus, because the modulus "
                        + "divides the period. Coverage makes the range the union of those "
                        + "intersections, so the period is at most the sum over the system of the "
                        + "period divided by each modulus. Dividing by the period gives the claim. "
                        + "Overlaps are permitted throughout, which is why the conclusion is an "
                        + "inequality and not an equality."))),
                DescribeRole.Theorem)),
        []));
}
