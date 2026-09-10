using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ConstantEqualSumDivisorIdentityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/wiseman2025a383093");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The divisor sum of partition counts with an equal-sum constant-block decomposition "
            + "counts all such block systems.",
        H("Constant Blocks with a Common Sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("capable-divisor-sum"),
            DeclarationHandle.Create(
                "D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.capable_divisor_sum"),
            H("The A383093 divisor identity"),
            StatementSource.FromAuthor(IdentityFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Here a(d) counts unlabeled integer partitions of weight d for which "
                    + "a decomposition into constant blocks with a common sum exists. "
                    + "The function s(n) counts all block multisets of weight n, as in "
                    + "A323774. The OEIS entry states this identity as a conjecture.")),
                Paragraph(Text(
                    "A system is recorded by its positive common sum D and a multiset of "
                    + "positive block values dividing D. Each occurrence of x denotes one "
                    + "block of D/x copies of x. The proof checks flattening, weight, and "
                    + "unique recovery of this multiset from the partition and D. "
                    + "The two counts are defined independently.")),
                Paragraph(Text(
                    "For a flattened partition let L be the lcm of its support. Every "
                    + "admissible common sum is tL. The equal-sum condition forces t to "
                    + "divide every multiplicity. Dividing those multiplicities by t "
                    + "preserves the support and produces a capable partition of weight "
                    + "n/t with common sum L. Conversely, scaling a capable partition "
                    + "of weight d by n/d gives a system of weight n. The lcm of the "
                    + "unchanged support recovers the scaling factor, making these "
                    + "constructions inverse. Taking finite cardinalities proves the "
                    + "identity for positive n. The empty system is counted separately."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula IdentityFormula() => Disp(Seq(
        Forall, Sp, V("n"), InMacro, Mathbb, Grp(V("N")), Comma, Sp,
        D(0), Lt, V("n"), Sp, Implies, Sp,
        Sum, Underscore, Grp(Seq(V("d"), Mid, Sp, V("n"))),
        V("a"), Open, V("d"), Close, Sp, Eq, Sp,
        V("s"), Open, V("n"), Close));
}
