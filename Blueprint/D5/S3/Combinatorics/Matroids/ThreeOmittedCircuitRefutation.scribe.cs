using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class ThreeOmittedCircuitRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three omitted bases can impose dependent restrictions on the joint lifting obstruction.",
        H("Three Omitted Uniform Bases Can Interact"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-replacement-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Independent cyclic-factor replacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For three rank-sized omissions with pairwise intersection of cardinality at most "
                    + "the rank minus two, the proposed decomposition removes three factors of each "
                    + "of the two uniform orders and adds one factor for each omission. The replacement "
                    + "order is the gcd of the total size and the class sizes outside that omission. "
                    + "The rank is at least three and the corank is at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-omissions-refutation"),
                DeclarationHandle.Create(Module + ".result"),
                H("Dependent restrictions in rank four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Partition six singleton classes into three pairs and omit the union of each two pairs "
                    + "from the rank-four bases. Each permitted basis contains exactly one complete pair. "
                    + "Give the three types binary coefficients u, v and u+v. The weighted boundary and "
                    + "signed deletion rows vanish for every choice of u and v. Two basis readouts recover "
                    + "the parameters, so the joint lifting obstruction has at least four elements killed "
                    + "by two. The proposed decomposition is cyclic of order six, with exactly two such elements."))),
                DescribeRole.Theorem))));
}
