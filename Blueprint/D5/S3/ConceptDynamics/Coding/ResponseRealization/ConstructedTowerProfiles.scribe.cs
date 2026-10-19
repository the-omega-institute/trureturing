using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseRealization;

internal sealed class ConstructedTowerProfilesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing two-sided reduction has paired split kinds and exact incoming and outgoing counts on both constructed towers.",
        H("Profiles of the towers actually constructed by reduction"),
        Blocks(
            Paragraph(Text("TwoSidedFiniteInduction.Presentation bundles actual finite essential graphs, decidable equality and a discrete edge topology; empty carriers are permitted. Given F,H, a graph Code c, a history homeomorphism P with its one-block equation hP, and a total inverse table Q with radii M,N and exact all-history recovery hQ, reduce k F H c P hP M N Q hQ hk constructs the two towers, where hk states M+N=k. The radii need not be minimal.")),
            Paragraph(Text("kinds records true for outgoing and false for incoming in traversal order. Profile records five separate facts: left incoming=M, left outgoing=N, right incoming=M, right outgoing=N, and equality of the complete kind lists. Strong induction follows the existing recursion: an outgoing step decreases N, an incoming step at N=0 decreases M, and the zero case is the existing finite relabeling. Thus the matching profiles are conclusions about these towers, rather than a pairing premise.")),
            Paragraph(Text("SplitTowerPositiveAccounting.terminal_literal has correction minus left incoming count minus right outgoing count. The first and fourth Profile fields turn that correction into -(M+N)=-k. Equal total lengths alone do not justify that substitution. The response terminal includes a first outgoing split before its reduce tail; response_profile therefore has M=a+c and N=b+d+1, retaining that extra one.")),
            Paragraph(Text("The output time correction uses the left incoming and right outgoing counts. The full profile also retains both complementary counts and equality of the split-kind lists; equality of total lengths alone does not determine the correction.")),
            Describe.Remark(DescribeId.Create("response-realization-constructed-tower-profiles-kinds"), DeclarationHandle.Create(Prefix + "kinds"), H("kinds"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This recursively reads the actual Tower constructors into a List Bool. It is consumed in Profile and in each induction branch of reduce_profile and response_profile; it introduces no alternative tower syntax.")))),
            Describe.Remark(DescribeId.Create("response-realization-constructed-tower-profiles-profile"), DeclarationHandle.Create(Prefix + "Profile"), H("Profile"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the five-clause proposition about one constructed Terminal and two natural radii. Keep all four count equalities and the kind-list equality. The response arithmetic later projects only its first and fourth clauses.")))),
            Describe.Lean(DescribeId.Create("response-realization-constructed-tower-profiles-reduce-profile"), DeclarationHandle.Create(Prefix + "reduce_profile"), H("reduce_profile"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Follow the outgoing, incoming and zero branches of the same reduce recursion to obtain both tower profiles and equality of their split-kind lists. The response profile then includes its first outgoing step."))), DescribeRole.Theorem),
            
            Describe.Lean(DescribeId.Create("response-realization-constructed-tower-profiles-response-profile"), DeclarationHandle.Create(Prefix + "response_profile"), H("response_profile"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("On the actual response terminal, both towers have incoming count a+c and outgoing count b+d+1 and the same split-kind list. It explicitly prepends the completed first outgoing stage to the tail profile. output_literal consumes the incoming-left and outgoing-right equalities."))), DescribeRole.Theorem))));
}
