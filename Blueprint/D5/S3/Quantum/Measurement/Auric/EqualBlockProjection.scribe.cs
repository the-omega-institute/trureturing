using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class EqualBlockProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp attained entropy gain of a flat-rank state under three equal coordinate blocks",
        H("Flat-rank states and equal coordinate blocks"),
        Blocks(Describe.Lean(
            DescribeId.Create("is-greatest-flat-record-gain"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/EqualBlockProjection.isGreatest_flat_record_gain"),
            H("Exact attained coordinate pinching gain"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Quantum/aberg2006superposition"),
                LibraryNoteRef.Create("D5/L/Quantum/lipoon2003principalsubmatrices"),
                LibraryNoteRef.Create("D5/L/Quantum/massey2010noncommutativeschurhorn")),
            Blocks(
                Paragraph(Text("Fix three coordinate fibers each of size m > 0. Optimize the von Neumann entropy gain of their coordinate pinching channel over P/r, where P is a Hermitian projection of rank 1 ≤ r ≤ 3m and every diagonal entry is r/(3m).")),
                Paragraph(Text("Let d = min(r, 3m − r), ℓ = max(d − m, 0), and b = d − 3ℓ. When 2r ≤ 3m the attained gain is (3ℓ log 2 + b log 3)/r. When 2r > 3m it is (3ℓ log 2 + 2b log(3/2))/r. In particular the gain is zero at full rank.")),
                Paragraph(Text("Use an isometric frame for P in the first case and for its complement in the second case. Its coordinate row blocks have positive Gram effects summing to identity, each with trace d/3 and rank at most m. The pinched matrix is the direct sum of the row products or their complements. Rectangular Gram products have the same nonzero eigenvalues with multiplicity. The two scalar objectives vanish at zero, and trace preservation cancels the logarithm of the normalization, yielding the spectral objective divided by the original rank r.")),
                Paragraph(Text("To realize the maximum, factor each attaining effect through m rows, assign its nonzero eigenvectors to distinct Fourier columns, and use the normalized Fourier rows to make every diagonal entry of the row product equal to its trace divided by m. Stack the resulting rows in the given fibers. Their Grams sum to identity, so the stack gives the required projection or complementary projection with the prescribed diagonal.")),
                Paragraph(Text("Åberg supplies the entropy-gain interpretation, with the projective embedding extension due to Bischof, Kampermann and Bruß. Li and Poon and Massey give the broader spectral feasibility context. The equal-block maximum follows from the rank-capped effect theorem and the explicit Fourier realization."))),
            DescribeRole.Theorem))));
}
