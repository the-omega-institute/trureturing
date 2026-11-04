using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostStateFieldLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed locality for every homogeneous state in the actual ghost Fock space.",
        H("Actual ghost superlocality"), Blocks(
            Paragraph(Text("The normal product has a signed reverse half. Its three-field discrepancy is the signed double commutator. The sign-independent finite-residue cancellation kernel from FieldNormalProductLocality is reused with these exact signed coefficients. No ordinary plus-ordered normal product is identified with odd normal ordering.")),
            Describe.Lean(DescribeId.Create("bc-state-field-signed-locality"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality.stateField_locality"),
                H("Homogeneous all-state signed locality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The locality order is uniform in the vector on which the modes act. Actual b and c CAR, divided derivatives and signed Dong closure give locality of sorted creator words. Finite occupation support and actual parity extend this to every homogeneous finite linear combination. The statement is algebraic formal-field locality, without a physical spacetime interpretation."))),
                DescribeRole.Theorem))));
}
