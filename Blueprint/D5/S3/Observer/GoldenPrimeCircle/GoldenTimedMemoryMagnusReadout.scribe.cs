using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenTimedMemoryMagnusReadoutDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenTimedMemoryMagnusReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar golden phase endpoint forgets short-long order, while the prime half-beat second-Magnus readout detects every nonzero time-ordered memory curvature and reverses sign under event exchange.",
        H("Golden Timed-Memory Magnus Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-invisible-noncommutative-visible"),
                DeclarationHandle.Create(
                    Prefix + "scalar_invisible_noncommutative_visible"),
                H("Abelian invisibility and noncommutative visibility"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("scalarEndpoint")), Sp,
                    Eq, Sp, Operatorname, Grp(F.Id("swappedScalarEndpoint")),
                    Comma, Sp, Operatorname, Grp(F.Id("MagnusReadout")), Sp,
                    Neq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At the calibrated half beat, the complete witness factors as two times a unit short-channel phase times the frozen prime swap curvature. Its norm is therefore exactly twice the curvature norm.")),
                    Paragraph(Text(
                        "The scalar phase product remains unchanged when the two frequency letters are exchanged. The matrix-memory step-two logarithm remains oriented, and exchanging the timed events negates the witness."))),
                DescribeRole.Theorem))));
}
