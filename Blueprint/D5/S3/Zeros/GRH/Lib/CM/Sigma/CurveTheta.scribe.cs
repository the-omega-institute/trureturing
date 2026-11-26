using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.Sigma;

internal sealed class CurveThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Curve Theta", H("Curve Theta"),
        Blocks(
            Paragraph(Text("Weierstrass functions cover the cubic; sigma doubling; zeros and derivative of ℘'. Taylor series, normalised CM lattice, theta function and coordinates at a 2-torsion origin. Generator of the imaginary quadratic integer ring; stability under conjugation. Lattice invariants via E4, E6, discriminant; uniformisation of elliptic curves. CM lattices correspond to scaled fractional ideals; existence and area formula. Theta function shifted by a two-torsion point: cubic, addition, doubling, multiplier.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/Sigma/CurveTheta.comp_mul_mem_sections"),
                H("comp_mul_mem_sections"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let C, C′ be CM data for a prime d ≡ 7 mod 8, with aΛ ⊂ Λ′ and a·ā·area(Λ) = N·area(Λ′), N natural. If g is a section of degree k for C′, then z ↦ g(az) is a section of degree kN for C.")))))));
}
