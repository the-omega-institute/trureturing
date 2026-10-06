using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class SemiprimeDivisorRepairRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation.";
    private static readonly LibraryNoteRef BooleanSource =
        LibraryNoteRef.Create("D5/L/Certificates/abbasizanjanikullmann2020twocnf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six congruence packets with distinct semiprime anchors have incompatible "
            + "divisor phases. Even arbitrary output residues cannot repair their "
            + "whole union at the prescribed ternary height.",
        H("A Semiprime Divisor Repair Obstruction"),
        Blocks(
            Entry("anchor", "Six semiprime anchors",
                "In order, the anchors are 35, 77, 55, 65, 221 and 85. "
                    + "Each anchor is the product of two different primes from "
                    + "the set {5,7,11,13,17}.",
                DescribeRole.Definition),
            Entry("literal", "Literal source residues",
                "The corresponding residues are 36, 441, 396, 495, 936 and zero. "
                    + "Every residue is divisible by nine. The source packet with "
                    + "anchor m and residue a contains precisely the integers "
                    + "congruent to zero modulo nine and to a modulo m.",
                DescribeRole.Definition),
            Entry("bank", "The numerical divisor bank",
                "The bank is {1,5,7,11,13,17,35,55,65,77,85,221}, the union "
                    + "of the divisors of the six anchors. A donor d supplies "
                    + "one output modulus 27d, with one freely chosen residue.",
                DescribeRole.Definition),
            Entry("claim", "A simultaneous repair of the packet union",
                "There exists one function r from natural numbers to natural "
                    + "numbers such that every integer in each of the six source "
                    + "packets is congruent to r(d) modulo 27d for some d in the "
                    + "bank. The residue assigned to a numerical donor is shared "
                    + "by all six packets. Unreduced natural residues represent "
                    + "all possible integer residue classes.",
                DescribeRole.Definition),
            Entry("result", "No output phase assignment covers the union",
                "The simultaneous repair claim is false. On a child of an "
                    + "anchor-m packet, the portion covered by a donor not "
                    + "dividing m has relative upper density at most gcd(m,d)/d. "
                    + "The six sums of these upper bounds "
                    + "are respectively 1334/2431, 848/1105, 1090/1547, "
                    + "860/1309, 344/385 and 712/1001, all strictly below one. "
                    + "The reciprocal-modulus covering bound therefore forces "
                    + "some divisor of m to contain each entire child. The "
                    + "unit and m can serve at most two of its three children, "
                    + "so at least one endpoint prime must match its literal "
                    + "phase. The first three packets force the phase modulo "
                    + "five to be one; the last three force it to be zero. "
                    + "Their Boolean consequence is the known U-zero(5,3) "
                    + "clause set in Abbasizanjani and Kullmann, Section 4. "
                    + "The Boolean variables mean that the prime phases equal "
                    + "one; phase zero implies the corresponding negation. "
                    + "This implication allows arbitrary other residues. "
                    + "The result concerns this fixed finite source union and "
                    + "this bank. It neither constructs an odd covering system "
                    + "nor excludes repairs using additional numerical donors.",
                DescribeRole.Theorem, acknowledge: true))));

    private static DocumentBlock Entry(string name, string heading, string prose,
        DescribeRole role, bool acknowledge = false) =>
        Describe.Lean(
            DescribeId.Create("semiprime-divisor-repair-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.WithoutFormula(),
            acknowledge ? AssessedProvenance.FromRepo(BooleanSource) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
