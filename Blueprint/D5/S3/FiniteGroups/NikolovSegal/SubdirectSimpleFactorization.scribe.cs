using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SubdirectSimpleFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prescribed nonabelian simple quotient of a finite subdirect product factors through one coordinate.",
        H("Simple quotients of finite subdirect products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-subdirectsimplefactorization-subdirect-simple-factorization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SubdirectSimpleFactorization.subdirect_simple_factorization"),
                H("Factorization of the prescribed quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let B be an actual subgroup of a finite dependent product of groups, and suppose that every restricted coordinate projection is surjective. Fix a surjective homomorphism theta from B onto a nonabelian simple group F. There is a coordinate i and a homomorphism from the whole factor A i to F whose composite with the restricted coordinate projection is theta. Neither the factor groups nor F is required to be finite.")),
                    Paragraph(Text("The proof treats finite jointly separating families of homomorphisms. After splitting off one coordinate, the other coordinates are replaced by their actual joint range. The two resulting kernels commute. Their images under theta are normal in F, and simplicity makes each image trivial or all of F. Both images cannot be all of F, since that would make F abelian. Thus theta descends through one of the two maps. Descent through the joint range reduces the number of coordinates; its coordinate maps remain surjective. The empty family would make the source trivial, contrary to surjectivity onto F.")),
                    Paragraph(Text("The joint range may be a proper subgroup of the remaining product. Keeping that range preserves all compatibility conditions among the coordinates. The resulting statement concerns the original homomorphism theta, rather than merely an unspecified simple section of some factor. It is an abstract group statement and supplies no geometric realization of a surface quotient or an outer action."))),
                DescribeRole.Theorem))));
}
