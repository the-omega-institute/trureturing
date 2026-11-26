using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Periods;

internal sealed class BesselIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Integral", H("Bessel Integral"),
        Blocks(
            Paragraph(Text("Heisenberg cocycle and translations on Hom in rational coordinates; kernels and theta-lift predicate. Eichler maps; integral over the Bessel quotient reduced to the definite unitary quotient.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Periods/BesselIntegral.integral_besselMeasure_eq_of_mean"),
                H("integral_besselMeasure_eq_of_mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For distinct grade 1 indices v, one κ gives ∫_{[B]} φ = κ∫_{[U(X)]} M whenever φ is continuous on U(V)(𝔸), left invariant under rational points of B, and φ(na) = f_a(c·(n − 1)_{v,X}) for unipotent n, f_a continuous periodic of mean M(a), M continuous on [U(X)].")))))));
}
