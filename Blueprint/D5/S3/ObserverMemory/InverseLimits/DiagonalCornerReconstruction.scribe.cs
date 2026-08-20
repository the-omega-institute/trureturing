using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class DiagonalCornerReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate corners recover every transition of a transfer operator.",
        H("Diagonal Corner Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-corner-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction"
                        + ".diagonal_corner_reconstruction"),
                H("Diagonal corner reconstruction formula"),
                StatementSource.FromAuthor(CornerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary state type Y and map tau, the basis vector at y is "
                            + "the finitely supported unit coordinate. The coordinate projection "
                            + "is evaluation at y followed by injection into that coordinate.")),
                    Paragraph(Text(
                        "The imported transfer operator is constructed from the source map by "
                            + "Finsupp.lmapDomain. Its action on a unit coordinate is exactly the "
                            + "unit coordinate at the image state.")),
                    Paragraph(Text(
                        "Composing the source-coordinate projection, transfer, and target-coordinate "
                            + "projection leaves the image basis vector when z is tau(y). The exact "
                            + "coordinate evaluation lemmas make the composition zero otherwise, "
                            + "which also proves the nonzero criterion."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CornerFormula()
    {
        Formula stateType = F.Id("Y");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula projectionY = new Formula.Subscript(F.Id("P"), y);
        Formula projectionZ = new Formula.Subscript(F.Id("P"), z);
        Formula transfer = new Formula.Subscript(F.Id("L"), Tau);
        Formula basisY = new Formula.Subscript(F.Id("e"), y);
        Formula basisZ = new Formula.Subscript(F.Id("e"), z);
        Formula corner = Seq(projectionZ, transfer, projectionY);
        Formula image = Call(Tau, y);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp,
            Forall, Sp, Tau, Colon, Sp, stateType, Sp, To, Sp, stateType,
            Comma, Sp, Forall, Sp, y, Comma, Sp, z, Sp, InMacro, Sp,
            stateType, Comma, RowBreak,
            Open, corner, Sp, Neq, Sp, D(0), Sp, Iff, Sp,
            z, Sp, Eq, Sp, image, Close, Sp, Land, RowBreak,
            Open, z, Sp, Eq, Sp, image, Sp, Rightarrow, Sp,
            corner, basisY, Sp, Eq, Sp, basisZ, Close, Sp, Land, RowBreak,
            Open, z, Sp, Neq, Sp, image, Sp, Rightarrow, Sp,
            corner, Sp, Eq, Sp, D(0), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
