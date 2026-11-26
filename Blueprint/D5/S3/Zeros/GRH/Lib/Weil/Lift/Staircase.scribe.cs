using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Lift;

internal sealed class StaircaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Staircase", H("Staircase"),
        Blocks(
            Paragraph(Text("Holomorphic Fock vectors and kernels; automorphic functions of a level, basic API. Dictionary between residue-matrix functions, moduli and named Weil data; finite Fourier expansion. A rapidly decreasing function of a level times a theta kernel keeps both properties. Products of minors are joint harmonic highest vectors for (U(p,q), U(n)), Kashiwara–Vergne.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase.staircase_harmonic_highest"),
                H("staircase_harmonic_highest"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Staircases: the product of k(η, p) copies of the p × p minor on the first p columns of sign η and the first (η = 1) or last p rows is, if the sizes fit, nonzero, harmonic and highest on both sides, of explicit weights.")))))));
}
