using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinLargeTransferCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinLargeTransferCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source vector identities with exact integer lags.",
        H("Continuation polynomials"),
        Blocks(
            Node("row5-lags", "rowFiveCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 10 are (6, 31, −97, −163, 417, 93, −514, 192, 72, −36)."),
            Node("row5", "rowFive", "Full-state relation at height 5", DescribeRole.Theorem,
                "On all 243 unrestricted columns at height 5, the power at exponent 11 on ones equals the source lag-weighted sum of the power vectors at exponents 10 down to 1. The coefficient sum is one."),
            Node("row7-lags", "rowSevenCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 47 are (16, 196, −3074, −10566, 216596, 78746, −7555872, 9810518, 143284008, −357710825, −1495653319, 5688279614, 7841029858, −51325489356, −6388247723, 287774292823, −176104268208, −0xf329324f36, 0x11d53a7aba4, 0x23f76e32e2f, −0x3f99620d7b9, −0x352695bd558, 0x91834a724fc, 0x26af1398425, −0xe4e3e053fa0, 0x107f904a101, 0xfed1c63947e, −0x4cdafc801b8, −0xcad68e2a227, 0x60f61784666, 0x7302409faae, −0x4908fef0104, −0x2d86ef2526c, 0x24aedad60d0, 823313870004, −866028504844, −126258454484, 202072349924, 5321968504, −31031088088, 1747695584, 2945878288, −337788928, −153195552, 23841280, 3259008, −599040)."),
            Node("row7", "rowSeven", "Full-state relation at height 7", DescribeRole.Theorem,
                "On all 2187 unrestricted columns at height 7, the power at exponent 48 on ones equals the source lag-weighted sum of the power vectors at exponents 47 down to 1. The coefficient sum is one."),
            Node("column5-lags", "wordFiveCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 7 are (15, −59, 60, 21, −55, 21, −2)."),
            Node("column5", "wordFive", "Full-state relation at width 5", DescribeRole.Theorem,
                "On all 48 proper words at width 5, the power at exponent 7 on ones equals the source lag-weighted sum of the power vectors at exponents 6 down to 0. The coefficient sum is one."),
            Node("column6-lags", "wordSixCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 10 are (19, −74, −25, 361, −268, −271, 337, −54, −29, 5)."),
            Node("column6", "wordSix", "Full-state relation at width 6", DescribeRole.Theorem,
                "On all 96 proper words at width 6, the power at exponent 10 on ones equals the source lag-weighted sum of the power vectors at exponents 9 down to 0. The coefficient sum is one."),
            Node("column7-lags", "wordSevenCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 20 are (42, −590, 3167, −1918, −37505, 95138, 67348, −449955, 266387, 629595, −841378, −28007, 588908, −332461, 7999, 44409, −11184, −342, 380, −32)."),
            Node("column7", "wordSeven", "Full-state relation at width 7", DescribeRole.Theorem,
                "On all 192 proper words at width 7, the power at exponent 20 on ones equals the source lag-weighted sum of the power vectors at exponents 19 down to 0. The coefficient sum is one."),
            Paragraph(Text("The verified multiset of successor classes gives the exact quotient action on each actual state. The checked power table begins at one on every class, and each row is obtained by multiplying by its quotient matrix. The final vector relation pulls back through the class map to the actual source states."))
        )));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
