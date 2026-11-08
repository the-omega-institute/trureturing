using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentBandDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fourth moments of fixed increments on an exponent band.",
        H("The fourth-moment band hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourth-moment-band-bound-for"),
                DeclarationHandle.Create(Prefix + "FourthMomentBandBoundFor"),
                H("Uniform fourth-moment upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write D_u(x)=E(x+u)-E(x). The constant C4 is nonnegative, and "
                    + "for all sufficiently large Y, simultaneously for every "
                    + "Y^alpha<=u<=Y^beta, the integral of abs(D_u(x))^4 from "
                    + "1 to Y is at most C4*Y*u^2*log(Y/u)^2. The threshold "
                    + "for Y is independent of u. This is the undivided form "
                    + "of the fourth-moment hypothesis."))),
                DescribeRole.Definition))));
}
