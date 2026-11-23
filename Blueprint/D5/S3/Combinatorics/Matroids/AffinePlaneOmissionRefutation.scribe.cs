using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class AffinePlaneOmissionRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-three affine lines can impose dependent restrictions on circuit lifting.",
        H("The Affine-Plane Omission Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-plane-replacement-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Independent replacement for the affine lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the nine points of the affine plane of order three with singleton parallel classes. "
                    + "For the rank-three matroid whose bases are precisely the triples other than the twelve affine lines, "
                    + "the proposed formula gives nine cyclic factors of order nine."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("affine-plane-omission-refutation"),
                DeclarationHandle.Create(Module + ".result"),
                H("Dependent restrictions in rank three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The twelve omitted lines meet in at most one point per pair and have empty total intersection. "
                    + "A finite coefficient certificate gives eleven vectors over the field of order three. "
                    + "The signed deletion and extension rows vanish on each vector. "
                    + "Eleven basis coordinates recover the independent parameters, so the integral lifting obstruction has "
                    + "at least three to the eleventh elements killed by three, whereas the proposed product has only three to the ninth."))),
                DescribeRole.Theorem))));
}
