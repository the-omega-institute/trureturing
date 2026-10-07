using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class UniformTwistedSmallLargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional all-simple small-large extension.",
        H("Conditional all-simple small-large extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-uniformtwistedsmalllarge-uniform-twisted-at-max-of-large-scalar-one"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/UniformTwistedSmallLarge.uniform_twisted_at_max_of_large_scalar_one"),
                H("uniform twisted at max of large scalar one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At fixed M and C, assume only the literal large-simple q=1 scalar PRODUCT input with genuine pre-target corrections. Small simple groups use proved bounded cardinality coverage; larger simple groups use Lemma 4.1. Identity padding yields a common length max(M,C+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-uniformtwistedsmalllarge-uniform-all-simple-twisted-of-large-scalar-one"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/UniformTwistedSmallLarge.uniform_all_simple_twisted_of_large_scalar_one"),
                H("uniform all simple twisted of large scalar one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If some M and C satisfy the still-open uniform large-simple scalar-one PRODUCT premise, a positive common twisted length exists for every finite noncommutative simple group. The uniform length precedes every group, arbitrary automorphism tuple and target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
