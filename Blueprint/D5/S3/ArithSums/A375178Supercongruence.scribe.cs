using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A375178SupercongruenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2024a375178");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A375178 binomial cube sum is one modulo the fifth power of every prime at least seven.",
        H("A375178: a fifth-power supercongruence"),
        Blocks(
            Paragraph(Text(
                "The sequence sums the cubes of choose(n+k-1,k) over natural k<n, "
                    + "including the empty sum at n=0. The theorem proves the p^5 "
                    + "conjecture in the OEIS comment for every prime p at least 7.")),
            Describe.Lean(
                DescribeId.Create("a375178-supercongruence"),
                DeclarationHandle.Create("D5/S3/ArithSums/A375178Supercongruence.supercongruence"),
                H("Universal congruence"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Oeis),
                Blocks(
                    Paragraph(Text(
                        "Work in ZMod(p^5). For 0<k<p, expand the binomial coefficient "
                            + "as p/k times the product of 1+p/j for 1<=j<k. After cubing, "
                            + "only the constant and linear terms of that product remain.")),
                    Paragraph(Text(
                        "Pairing k with p-k reduces the cubic harmonic sum modulo p^2 "
                            + "to the fourth-power sum modulo p. For the other term, reversal "
                            + "identifies the double harmonic sums H(1,3) and H(3,1). Their "
                            + "shuffle identity and the vanishing first and fourth power sums "
                            + "make both zero modulo p. The pinned finite-field power-sum "
                            + "theorem supplies these single sums.")),
                    Paragraph(Text(
                        "The OEIS entry supplies the conjecture. Zhao's multiple harmonic "
                            + "sum results cover the harmonic prerequisites in the literature; "
                            + "the argument here proves them locally in Lean and connects "
                            + "them to the binomial sum. The conjectures for prime powers "
                            + "and the generalized family are separate questions."))),
                DescribeRole.Theorem))));
}
