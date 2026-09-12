using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class JacoExponentialDominationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/JacoExponentialDominationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kok2025jaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A000149 vertices miss the closed neighborhood of vertex 88, so they do not "
            + "dominate the infinite linear Jaco graph.",
        H("Kok Conjecture 2.12 refutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("jaco-exponential-domination-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed exponential dominating set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 2.12 on printed page 9 of arXiv:2507.16500v1 proposes "
                        + "that the vertices indexed by A000149 dominate the infinite "
                        + "linear Jaco graph. The formal definition uses the natural "
                        + "floors of powers of e, indexed from exponent zero, and the "
                        + "paper's recursive right endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-exponential-domination-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Vertex 88 is not dominated"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The recursive endpoint certificate gives right endpoint 143 "
                            + "at vertex 88, while every vertex through 54 has right "
                            + "endpoint below 88. Thus the closed neighborhood of vertex "
                            + "88 is contained in the interval from 55 through 143.")),
                    Paragraph(Text(
                        "Mathlib's certified decimal bounds for e imply e to the fourth "
                            + "power is below 55 and e to the fifth power is above 144. "
                            + "Monotonicity of powers and natural floors then excludes every "
                            + "term of A000149 from that interval. Consequently vertex 88 "
                            + "is neither selected nor adjacent to a selected vertex. The "
                            + "result refutes only the printed conjecture; it gives no value "
                            + "for the domination number and proposes no replacement set."))),
                DescribeRole.Theorem))));
}
