using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class LatticeHalfFockGroundCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charge-character covariance of the complete corrected twisted field.",
        H("Ground exchange through every corrected-field coefficient"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank integral symmetric even lattice datum, "
                + "hu:IsUnit D.G.det, and a any lattice charge. Write G_a for the existing "
                + "actualGroundInsert D hu (groundAction D hu a), and chi_a for the ordinary "
                + "charge character in Lattice/NormFourPeirceInvolution. Its value on charge b "
                + "is multiplication by paritySign(bilinear D a b). The ordinary carrier and "
                + "the actual twisted tensor carrier are different spaces.")),
            Describe.Lean(
                DescribeId.Create("corrected-field-ground-character"),
                DeclarationHandle.Create(Prefix + "correctedField_ground_character"),
                H("Ground insertion implements the ordinary character on the full corrected field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every source v, integer Hahn exponent e and actual "
                    + "tensor vector x, G_a((correctedField v).coeff e x) equals "
                    + "(correctedField (chi_a v)).coeff e (G_a x). No norm-four assumption, "
                    + "preferred model, source identification, fixedness, parity, mode covariance "
                    + "or commutator premise is supplied. The charged coefficient calculation "
                    + "uses the existing actual ground exchange. Ground insertion commutes "
                    + "with every tensor jet, so both normal-order branches retain that same "
                    + "charge phase for arbitrary words. Existing pointwise finite support "
                    + "moves insertion and scalar multiplication through the full word sums. "
                    + "Linearity extends this to every source polynomial, the actual finite "
                    + "Corr, every shift and the complete finite charge sum."))),
                DescribeRole.Theorem),
            Paragraph(Text("The ordinary full-carrier, all-mode stateField_chi theorem remains "
                + "the ordinary supplier. Existing actualTensorL0_groundInsert_commute and "
                + "actualGroundInsert_preserves_grade already give energy and grade preservation. "
                + "The accepted NormFourFirstGradeSpectrum identification of the actual parity "
                + "minus grade with its physical space remains the spectral supplier. "
                + "No spectrum or numerical trace is reconstructed here.")),
            Paragraph(Text("For fixed-source physical applications, actualParity concerns "
                + "oscillator parity, whereas G_a acts on the ground factor. Source character "
                + "sign and target parity are distinct parameters. The existing fixedParitySlice "
                + "uses coefficient 2*e, so that is the coefficient to specialize in this "
                + "identity. Restricting carriers requires preserving source theta-fixedness "
                + "and target parity; this all-carrier coefficient theorem does not define a "
                + "new restricted field. Norm-four involutivity is a separate existing ground "
                + "square calculation, not a hypothesis of the character identity.")),
            Paragraph(Text("This is an all-integer-coefficient linear character identity, "
                + "derived from the classical lattice construction. It does not establish "
                + "VOA intertwining-operator Jacobi, orbifold gluing, all-grade Ising or Miyamoto "
                + "fusion, a Monster VOA, or the complete string-theory and AdS/CFT bridge. "
                + "Those objectives remain incomplete. No literature novelty is claimed.")))));
}
