using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class ProjectionDoesNotImplyClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete perfect coordinate projection has a range that a linear dynamics fails "
            + "to preserve.",
        H("Perfect Projection Does Not Imply Dynamical Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-coordinate-projection-is-perfect"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure."
                        + "firstCoordinateProjection_isPerfect"),
                H("The first-coordinate projection is perfect"),
                StatementSource.FromAuthor(FirstCoordinateProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The diagonal rational matrix with entries one and zero projects onto "
                            + "the first coordinate of the two-dimensional space. Multiplying "
                            + "this matrix by itself leaves it unchanged, so the projection is "
                            + "idempotent.")),
                    Paragraph(Text(
                        "The same matrix is equal to its conjugate transpose because it is real "
                            + "and diagonal. Idempotence together with this Hermitian symmetry "
                            + "makes it a perfect projection in the module's terminology."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("perfect-projection-does-not-imply-dynamical-closure"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure."
                        + "perfect_projection_does_not_imply_dynamical_closure"),
                H("A perfect projection need not have an invariant range"),
                StatementSource.FromAuthor(NonclosureWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are two-by-two rational matrices D and F for which D is a perfect "
                            + "projection but the range of D is not invariant under the linear "
                            + "dynamics induced by F. Thus projection perfection alone supplies "
                            + "no dynamical closure guarantee.")),
                    Paragraph(Text(
                        "The witnesses are the projection onto the first coordinate and the map "
                            + "sending the first basis vector to the second. The first basis "
                            + "vector lies in the projection range, while its image under the "
                            + "dynamics has a nonzero second coordinate and therefore lies outside "
                            + "that range."))),
                DescribeRole.Theorem))));

    private static Formula FirstCoordinateProjectionFormula() =>
        Disp(Seq(
            Call("IsPerfectProjection", F.Id("firstCoordinateProjection")), Dot));

    private static Formula NonclosureWitnessFormula()
    {
        Formula projection = F.Id("D");
        Formula dynamics = F.Id("F");
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula finTwo = Call("Fin", D(2));
        Formula matrix = Call("Matrix", finTwo, finTwo, rational);
        Formula projectionMap = Call("matrixToLinear", projection);
        Formula dynamicsMap = Call("matrixToLinear", dynamics);

        return Disp(Seq(
            Exists, Sp, projection, Comma, Sp, dynamics, Colon, Sp, matrix, Comma, Sp,
            Call("IsPerfectProjection", projection), Sp, Land, Sp,
            Neg, Sp, Call("IsInvariant", dynamicsMap, Call("range", projectionMap)), Dot));
    }
}
