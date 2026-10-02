using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteLocalLatitudeGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometry of the actual five two-qubit latitude records throughout the strict latitude interval.",
        H("FiniteLocalLatitudeGeometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("all-r-flat-geometry"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry.all_r_flat_geometry"),
            H("All latitude flat-response geometry"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every real r > 0 with 1/2 < r squared < 2, omega is exp(2 pi i/3), the source spinors are the two poles and (1, r omega to the j)/sqrt(1+r squared), j = 0, 1, 2, and each record is the tensor square of its source spinor. The symmetric coordinates b represent (b0, b1/sqrt(2), b1/sqrt(2), b2). Flat means equality of all five squared overlaps with these actual records.")),
                Paragraph(Text("Normalized symmetric flat vectors exist for every such r. Every normalized symmetric flat vector has all three squared coordinate moduli and all five responses equal to 1/3, and concurrence norm |b1 squared - 2 b0 b2| equal to kappa = sqrt(4+2(r squared+r to the minus two))/3. A unit flat product exists, and every unit flat product has all responses h = 1/(3(1+kappa)), antisymmetric weight g = kappa/(1+kappa), opposite polar heights and squared polar height 1-4h.")),
                Paragraph(Text("The Bloch matrices reuse the original trace-one qubit Bloch map. With Q(a,b) = rho(a) tensor rho(b), K_s consists of unit Bloch pairs whose five actual matrix responses equal h. K_s is nonempty, and every pair in K_s has a_z = -b_z, a_z squared = 1-4h, and (1-a dot b)/4 = g. Normalization and the determinant-zero product constraint establish the nonzero symmetric projection inside the proof. This result establishes the geometry prerequisite; it makes no claim about physical accepted recovery, Bellman values or a finite-protocol gap."))),
            DescribeRole.Theorem))));
}
