using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportCandidateCounterexamplesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportCandidateCounterexamples." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(text))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original failed sign rule and the entire persistent candidate-family rejection.",
        H("Divisor candidates do not determine the residual spectrum"),
        Blocks(
            Item("persistent-family", "persistent_family", "The full unbounded repeated-minimum candidate family",
                "For every integer k>=1, a=6k, b=a, c=(a-1)(2a-1) is an endpoint-one point and d=9k=3a/2 divides the exact quartic constant and lies in (b,2a). Nevertheless F(d)<0 and d squared does not divide N-Dd. The linear coefficient test therefore rejects that candidate throughout the entire stated family. The cancellation is valid for every k>=1, and the remaining contradiction is exact reduction modulo three. This excludes one candidate family, not all window divisors or all fully distinct exponent triples.", DescribeRole.Theorem),
            Item("opposite-sign-control", "opposite_sign_control", "The original exact two-sign control",
                "At the received repeated-exponent endpoint point (20,20,741), both 21 and 30 divide N and lie in the strict spectral window, with F(21)=1207587225600 and F(30)=-1257386661900. This consumed helper supplies the following full-surface refutation. The graph was already settled by the repeated-exponent theorem; no new graph nonintegrality family is asserted.", DescribeRole.Theorem),
            Item("uniform-negativity", "uniform_negativity", "The original full-surface negativity proposal",
                "The proposed rule quantifies over every ordered integer minimum-four endpoint-one triple and every constant divisor in the strict spectral window. It requires the residual quartic value to be negative at every such divisor.", DescribeRole.Definition),
            Item("refutation", "refutation", "Full-surface uniform negativity is false",
                "The actual endpoint polynomial and divisor at the original control refute this universal sign rule. Its restriction to fully distinct integer endpoint points is not decided here. The full higher-prime Q3 and integer-point feasibility boundaries remain as received.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic"))]));
}
