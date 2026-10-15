using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeBrstDifferentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Q on every basis vector of the entire exceptional sector.",
        H("Complete Native BRST Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-q-exceptional-basis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstDifferential.Q_sectorBasis"),
                H("One nonzero column"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    Call("Q", F.Id("D"), F.Id("H"), Call("basis", F.Id("i"))), Sp, Eq, Sp,
                    Call("exceptionalColumn", F.Id("i"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Assume H times gramComplex(D)=1 and gramComplex(D) times H=1. The only nonzero column is Q(Omega tensor c0 Omega)=2 Omega tensor c1 c(-1) Omega. Every other vector in the complete sector basis is killed.")),
                Paragraph(Text("For each matter axis the frequency-one excitation with c1 Omega is killed because the original matter L0 contribution is minus the {1,3} tensor and the ghost contribution is plus that same tensor. With the c0 creator also present both contributions vanish. Positive matter modes kill these charge-zero states, and the remaining negative-mode terms vanish by native c-mode support.")),
                Paragraph(Text("Here site 1 is c1, site 3 is c0, and site 5 is c(-1); the sector also includes the triple {1,3,5}. This matrix is derived after proving the complete energy fiber, not chosen as a model for it. No selected frame or nonzero charge pairing appears."))))
        )));
}
