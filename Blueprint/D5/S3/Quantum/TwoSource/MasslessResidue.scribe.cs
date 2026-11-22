using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TwoSource;

internal sealed class MasslessResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TwoSource/MasslessResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two normalized sources have mixed massless residue between minus and plus one half. Both endpoints determine the entire residue.",
        H("The mixed residue of two normalized sources"),
        Blocks(
            Describe.Lean(DescribeId.Create("balanced-residue"), DeclarationHandle.Create(Prefix + "balanced"),
                H("Balanced realization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This real symmetric matrix has diagonal entries one half and off-diagonal entries r."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sharp-mixed-residue"), DeclarationHandle.Create(Prefix + "sharp_mixed_residue"),
                H("Attainable mixed residues and rigidity at the endpoints"),
                StatementSource.FromAuthor(Disp(Seq(Minus, Frac, Grp(D(1)), Grp(D(2)), Sp, Le, Sp,
                    F.Id("r"), Sp, Le, Sp, Frac, Grp(D(1)), Grp(D(2))))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exists a real two-by-two positive semidefinite matrix Z with mixed entry r and positive semidefinite complement I−Z exactly when |r| ≤ 1/2. Each attainable r is realized by the balanced matrix. At either endpoint every such matrix equals that balanced realization.")),
                    Paragraph(Text("Evaluate both quadratic forms on (1,1) and (1,−1). These tests trap the trace between 2|r| and 2−2|r|. When |r|=1/2, the trace is one. Positivity of the determinant then forces each diagonal entry to be one half. Conversely the balanced quadratic form is a nonnegative weighted sum of the squares of the sum and difference of the coordinates. The complement is the balanced matrix with coefficient −r."))), DescribeRole.Theorem))));
}
