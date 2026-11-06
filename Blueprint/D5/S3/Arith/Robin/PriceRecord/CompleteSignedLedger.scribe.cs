using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;
internal sealed class CompleteSignedLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact full signed ledger at the same integer and cutoff.",
        Blocks(Describe.Lean(
            DescribeId.Create("same-integer-complete-signed-margin"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.robin_margin_eq_complete_signed_ledger"),
            H("The literal Robin margin identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real z>=4 and positive integer N with exactly the prime support p<=z, let M=log(N)-z and K=log(log(z))+M/(z*log(z))-log(log(z+M)). Then robinLogMargin(N)=WeightedTailTransport.weightedTail(CompleteMertensPeak.psiErrorKernel,z)+Delta_z(N)-K. Delta is the original Euler tail plus signed log(N)-psi(z) inventory minus the complete strict prime-power residual. The proof consumes the exact Mangoldt/Euler residual equality, the unconditional complete Mertens ledger, and the same-integer finite Euler identity. It adds no hLay, integrability, exponent, or residual-sign hypothesis, defines no substitute integral, and claims no opposite tail lower bound or RH conclusion."))), DescribeRole.Theorem))));
}
