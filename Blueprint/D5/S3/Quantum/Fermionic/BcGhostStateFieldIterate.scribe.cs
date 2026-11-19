using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostStateFieldIterateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed integer residue law of the actual occupation-state ghost fields.",
        H("Actual ghost integer iterate"), Blocks(
            Paragraph(Text("SignedFieldResidueLocality supplies the vectorwise finite residue constructor, all-integer signed locality, negative-residue formula and translation covariance. The local ResidueField interface projects its operator, coefficient identity and two finite-support proofs from that constructor. The reverse sum carries the product of the integer residue sign and the homogeneous parity sign. Creation on the actual vacuum and signed occupation-basis uniqueness identify the residue with the field of the actual mode product.")),
            Describe.Lean(DescribeId.Create("bc-state-field-signed-integer-iterate"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostStateFieldIterate.stateField_iterate"),
                H("All-integer signed iterate with actual finite sums"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every pair of homogeneous original Fock states, every third Fock state and both integer indices, both Ring.choose coefficient sums have finite support and their signed difference equals the mode of the field of the actual state product. There is no finite carrier truncation, supplied super vertex algebra or transported bracket. The conformal-state identification, cubic BRST zero mode, BRST derivation and later physical comparison and no-ghost results are separate obligations."))),
                DescribeRole.Theorem))));
}
