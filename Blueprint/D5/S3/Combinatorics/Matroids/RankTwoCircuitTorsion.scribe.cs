using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankTwoCircuitTorsionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized parallel-class potentials for rank-two joint restriction.",
        H("Class potentials for rank-two matroids"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("potentials-of-integral-readouts"),
                DeclarationHandle.Create(Module + ".exists_potentials_of_integral_readouts"),
                H("Recovering normalized class potentials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bases are the pairs of vertices from distinct parallel classes. The residue "
                    + "of a rational edge coefficient is taken in the sign convention of the vertex "
                    + "boundary. Integral readouts on pair circuits identify the edge residues along each "
                    + "parallel class. "
                    + "Triangle circuits make the residues differences of class values. Fixing the value "
                    + "of one class to zero makes these values unique. Every class value is killed by "
                    + "the ground size, and the sum weighted by class sizes vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-readouts-of-potentials"),
                DeclarationHandle.Create(Module + ".exists_integral_readouts_of_potentials"),
                H("Realizing normalized class potentials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose rational representatives of the class values and take their differences "
                    + "along the edges. The weighted equations make the resulting vertex boundaries "
                    + "integral. These boundaries sum to zero. Route the integral correction to one "
                    + "vertex along edges between classes, using a vertex in a second class when needed. "
                    + "Subtracting this correction gives a rational top cycle with the prescribed edge "
                    + "residues and integral readouts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-two-lifting-obstruction-potentials"),
                DeclarationHandle.Create(Module + ".rank_two_lifting_obstruction_potentials"),
                H("Class potentials and the lifting quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient of the saturated joint image by the original image is isomorphic to "
                    + "the module of normalized class potentials. The residue has zero class potential "
                    + "exactly when the rational source has integral edge coefficients. Every class "
                    + "potential satisfying the boundary relations is realized by one source cycle."))),
                DescribeRole.Theorem))));
}
