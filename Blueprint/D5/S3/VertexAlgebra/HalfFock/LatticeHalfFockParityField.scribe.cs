using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class LatticeHalfFockParityFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual target-parity transport for corrected half-Fock fields.",
        H("Target parity transport and fixed-source fields"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank integral symmetric even lattice datum and "
                + "hu:IsUnit D.G.det. The source Carrier D and target ActualTensor D hu remain "
                + "distinct. The target operator is the existing oscillator sigma tensored with "
                + "the identity on the actual quotient ground module. No positivity, Jacobi, "
                + "equivariance premise, conformal covariance or desired transport law is assumed.")),
            Describe.Lean(
                DescribeId.Create("corrected-field-target-parity"),
                DeclarationHandle.Create(Prefix + "correctedField_target_parity"),
                H("Corrected fields intertwine source theta with actual target parity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every source a, signed exponent e and actual target x, "
                    + "actualParity applied to the coefficient of correctedField a equals the "
                    + "coefficient of correctedField (theta a) applied to actualParity x. The "
                    + "proof starts with the charged oscillator kernel, propagates through the "
                    + "signed jet recursion and both flatCoefficient branches, then through the "
                    + "pointwise finite normal-word, correction and charge sums. Coordinate "
                    + "monodromy is not substituted for this target action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-parity-slice"),
                DeclarationHandle.Create(Prefix + "fixedParitySlice"),
                H("Fixed-source fields restrict to the actual parity sectors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For any s:Complex and fixed source a, paritySpace D hu s is "
                    + "the kernel of actualParity-s identity. The target/source identity proves "
                    + "that correctedField a preserves this subspace. fixedParitySlice uses the "
                    + "actual lower-truncated Hahn field and its original support bound, with "
                    + "coefficient 2*e for the integral-power restriction. Taking s=1 and s=-1 "
                    + "gives the two target parity sectors. This is a consumed "
                    + "sector action; it does not assert twisted Jacobi, an orbifold extension, "
                    + "fusion, Monster symmetry, string theory or AdS/CFT."))),
                DescribeRole.Definition),
            Paragraph(Text("Classical provenance: Dong--Nagatomo, math/9808088v1, section 3.2, "
                + "and Bakalov--Kac, math/0402315v1. The kernel calculation and its propagation "
                + "are repository-derived implementations of the existing lattice construction; "
                + "no literature novelty is claimed.")))));
}
