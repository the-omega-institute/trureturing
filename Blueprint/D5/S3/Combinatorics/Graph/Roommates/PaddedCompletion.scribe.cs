using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class PaddedCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial components of the Mertens range-two proof; the full theorem remains open.",
        H("PaddedCompletion"), Blocks(
            Describe.Lean(DescribeId.Create("oldposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldPosition"),
                H("oldPosition"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Place the left word at coordinates 0 through m-1 and the right word at m+6 through m+6+k-1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("oldoffset"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldOffset"),
                H("oldOffset"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Preserve every chosen displacement in the two input certificates, including zero for singles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("oldtarget"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldTarget"),
                H("oldTarget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Targets are integers, including all exterior requests. No quotient or truncation removes possible collisions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("requester"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.Requester"),
                H("Requester"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Select the actual old vertices whose nonzero requests enter the six-site gap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("request"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.request"),
                H("request"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translate each actual gap target to its buffer coordinate in Fin 6."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("old-target-injective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_target_injective"),
                H("old_target_injective"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full integer-target injectivity holds across both old pieces. Within one piece use its certificate; across pieces the left targets are at most m+1 and the right targets at least m+4."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("padded-request-completion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_request_completion"),
                H("padded_request_completion"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual gap requests are injective and avoid the two central buffer sites. Apply the existing sixteen-layout construction to obtain a genuine involution on requesters plus buffer, with only central new singles. This does not yet prove a certificate on the entire concatenated word or the padded count inequality."))), DescribeRole.Theorem))));
}
