using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveCRTMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chinese-remainder identities for finite sieve moments",
        H("Chinese-remainder identities for finite sieve moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centered-sieve-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments.centered_sieve_moment"),
                H("centered sieve moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural cutoff y and every finite set D of natural shifts, the expectation modulo the primorial of y of the product of the centered sieve variables indexed by D equals the inclusion–exclusion transform of the finite singular series on D. Chinese remaindering counts the simultaneous surviving residues prime by prime; the commutative-ring centered product expansion applied to each sieve variable plus one gives the stated transform."))),
                DescribeRole.Theorem))));
}
