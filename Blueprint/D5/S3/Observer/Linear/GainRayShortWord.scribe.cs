using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayShortWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Drift and rank for short literal words", H("Drift and rank for short literal words"), Blocks(
            Describe.Lean(DescribeId.Create("gain-ray-gainrayshortword-scalar-identity-read-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayShortWord.scalar_identity_read_bound"),
                H("A nonzero identity needs more reads than gain coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, word w, fixed Readout d w C, auxiliary real matrix S and nonzero real s, suppose C annihilates the vector of ones and response(d,w,C)(S)=s times the identity of size d+1. Then d+2 is at most length(w)+1. The identity makes C surjective onto all d+1 coefficient coordinates. The nonzero vector of ones lies in its kernel, so rank-nullity requires one additional input coordinate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayshortword-short-word-no-universal-success"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayShortWord.short_word_no_universal_success"),
                H("All rank-deficient short words are excluded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d at least one, every word w with length(w)+1 at most d+1, and every fixed C universally collinear on all World d, C succeeds at no World d. The statement includes mixed words, pure M words, pure J words and the empty action word, with the initial read included. This rank argument applies through d+1 reads."))), DescribeRole.Theorem))));
}
