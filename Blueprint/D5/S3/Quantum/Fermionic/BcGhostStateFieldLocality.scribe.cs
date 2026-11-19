using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostStateFieldLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed locality for every homogeneous state in the actual ghost Fock space.",
        H("Actual ghost superlocality"), Blocks(
            Paragraph(Text("SignedFieldNormalProductLocality supplies the signed commutator, signed normal-product locality and divided-derivative locality. Reflection of the coefficient indices transports the flip law from BinomialKernelDelta. The actual ghost CAR and occupation-word induction specialize this generic calculus to the original Fock carrier.")),
            Describe.Lean(DescribeId.Create("bc-state-field-signed-locality"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality.stateField_locality"),
                H("Homogeneous all-state signed locality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The locality order is uniform in the vector on which the modes act. Actual b and c CAR, divided derivatives and signed Dong closure give locality of sorted creator words. Finite occupation support and actual parity extend this to every homogeneous finite linear combination. The statement is algebraic formal-field locality, without a physical spacetime interpretation."))),
                DescribeRole.Theorem))));
}
