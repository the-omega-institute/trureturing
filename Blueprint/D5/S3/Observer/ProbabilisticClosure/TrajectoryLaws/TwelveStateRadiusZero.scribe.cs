using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateRadiusZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact native half-line posteriors and forcing risks", H("Exact native half-line posteriors and forcing risks"),
        Blocks(
            Paragraph(Text("All quantities use the original twelve-state parameter, its single stationary joint law J and visible pushforward P. The target bit is X0 and the native means retain the complete opposite half-line. Future recovery supplies Z1 only.")),
            Describe.Lean(DescribeId.Create("future-guess"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero.futureGuess"),
                H("The complete-future posterior version"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a joint trajectory the candidate is zero when X1 is one, and otherwise equals p evaluated at the original time-one hidden residue. The residue is readable from the whole future, without identifying its initial free or tail phase."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("past-guess"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero.pastGuess"),
                H("The complete-past posterior version"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The candidate is prob(H0,true): p_z on each free class and zero on each tail class. The past recovers Q0 on the same J."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-halfline-posteriors"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero.actual_halfline_posteriors"),
                H("Identification of the actual native radius-zero posteriors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under J, leftMean(parameter,0) pulled back along the visible coordinate equals futureGuess almost surely, and rightMean(parameter,0) equals pastGuess almost surely. The proof identifies their exact radius-zero observation fields with the complete future and complete past, proves the all-measurable-event integral identities using cylinder_future_law and full_past_future_factor, and applies conditional-expectation uniqueness. Thus the candidates are actual posteriors on P, rather than a separately specified conditional table."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-radius-zero-risks"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero.actual_radius_zero_risks"),
                H("Both exact radius-zero defects"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual leftRisk(parameter,0) and rightRisk(parameter,0) both equal 9/62. The native q=X0 identity and actual half-line posterior identities reduce the risks to expectations on J; the original two-edge cylinder weights evaluate both rational sums. In particular the actual radius-zero defects are strictly positive despite the zero full erased-bit loss."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-forcing-contributions"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateRadiusZero.actual_forcing_contributions"),
                H("Exact omitted-neighbor contributions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under P, the left squared defect at radius zero on X(-1)=1 integrates to 15/496, and the right squared defect on X1=1 also integrates to 15/496. On the original joint event H0=T0 and X1=0, the left squared defect integrates to 9/3968. Stationarity transports the actual one-edge relation to identify H0 phase with X(-1); all subsequent weights are original two-edge cylinder masses. These are contributions of omitted forcing neighbors, so no blanket forced-zero radius-zero defect follows."))), DescribeRole.Theorem),
            Paragraph(Text("The retained-neighbor application records the original qualification at every radius: the left native squared defect vanishes almost surely on X1=1, the right native squared defect vanishes almost surely on X(-1)=1, and at every positive radius n+1 both defects vanish on either forcing event. The no11 rule makes X0 zero there; measurability of the retained neighbor in the corresponding actual observation field and the conditional-expectation indicator identity give the native posterior-zero calculation on the same event. The radius-zero omission boundary is retained.")))));
}
