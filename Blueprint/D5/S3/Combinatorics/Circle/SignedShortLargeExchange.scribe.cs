using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class SignedShortLargeExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct an actual signed short-reserve return and consume it in the shared three-LARGE physical exchange.",
        H("Signed short mass for the complete three-LARGE exchange"),
        Blocks(
            Paragraph(Text("The source is the actual centered doubling source on physical Fin k labels. This result is conditional on an actual signed short reserve after x; it does not assert universal reserve availability, transport across earlier gates, deeper suffix completion or full C3.1.")),
            Describe.Lean(DescribeId.Create("signed-short-reserve-select"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SignedShortLargeExchange.signed_short_reserve_select"),
                H("Constructive signed short-reserve selector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a Nodup physical list T, P0 is a physical subpermutation of the entries with 0<f<=B+1 and N0 is a physical subpermutation of the entries with 0<-f<=B+1. Every positive entry of T is at most M, low>0 is supplied by the total positive mass, and the reserve resource is M-B-1 <= mass(P0)+mass(-f,N0).")),
                    Paragraph(Text("Remove P0 from the actual positive list and first-cross the remainder at low-Sp. If it undershoots, first-cross P0 at the deficit. If it lands in [low,low+B], retain it. If it overshoots, first-cross N0 with weights -f at u-low-B and append that negative correction. The resulting R is physical, has mass in [low,low+B], and K is the explicit complement with (R++K).Perm T.")),
                    Paragraph(Text("The selector uses only the existing PositiveSmallReturnExchange.first_crossing three times. Equal numerical values remain distinct occurrences; no subset-sum oracle or assumed return list is an input."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-source-three-large-signed-short-exchange-full"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SignedShortLargeExchange.actualSource_threeLarge_signed_short_exchange_full"),
                H("Signed selector consumed by the complete physical exchange"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the original actual-source gates, positive and negative short reserve subpermutations P0 and N0, a positive bound M for every actual positive SMALL entry, and M-(C-s(q))-1 <= mass(P0)+mass(-s,N0), the signed selector supplies a physical R with mass in [low,low+C-s(q)] for every demanded positive low covered by the positive mass.")),
                    Paragraph(Text("Nodup of the SMALL word is derived from its physical sublist inclusion in the original Legal word. The single tagged physical engine in ThreeLargePacketExchange is consumed with tag True; the existing positive return theorem consumes that same engine with tag R.Subperm(Pos). It returns the literal V=A++[p,n]++L++[z,q] and [x,y,zpen]++R, preserving the complete Inventory, every natural take bound, exact G/U/H balances, strict H and J descent, and endpoint in [s(q),C]. Negative labels in R are permitted. The theorem is conditional on these actual reserves and makes no universal availability, transport, deeper-tail, minimizer, or full C3.1 claim."))),
                DescribeRole.Theorem)), []));
}
