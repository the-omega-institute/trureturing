using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class StateFieldResidueReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/StateFieldResidueReconstruction.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted state fields are closed under every integer residue and satisfy the finite iterate identity.",
        H("State-Field Residues and the All-Integer Iterate Law"),
        Blocks(
            Paragraph(Text("Let V be the full complex module and let Y be the actual linear "
                + "state-field map. The hypotheses are primitive creation, creativity, "
                + "translation covariance and pairwise operator-uniform locality. The "
                + "construction uses pointwise finite sums on every actual vector, so it "
                + "does not form an infinite sum in End(V), assume Jacobi or associativity, "
                + "or replace V by a polynomial Fock carrier.")),
            Paragraph(Text("Primary attribution: Carpi--Codogni, arXiv:2605.26972v1, section 2.1, "
                + "equation (8), with the standard reconstruction argument. The cited "
                + "source motivates the mode formula; the declarations below are the "
                + "native unrestricted-carrier proofs and do not assert Moonshine "
                + "Conjecture 14.4.")),
            Describe.Lean(
                DescribeId.Create("state-field-residue-nonnegative-locality"),
                DeclarationHandle.Create(Prefix + "residue_nonnegative_locality"),
                H("Positive residues preserve uniform locality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For r at least zero, the residue coefficient is the "
                    + "rth finite difference of the actual commutator. The triple "
                    + "discrepancy is killed by the three pairwise locality polynomials; "
                    + "the finite binomial expansion gives an order independent of the "
                    + "input vector. The proof consumes the shift-intertwining helpers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("state-field-relative-vacuum-uniqueness"),
                DeclarationHandle.Create(Prefix + "relative_vacuum_uniqueness"),
                H("Creative covariant local fields are uniquely reconstructed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("A field with zero nonnegative and minus-one vacuum "
                    + "coefficients, translation covariance and locality against every "
                    + "existing Y-state field is zero. The negative vacuum coefficients "
                    + "are obtained by the translation recurrence, and locality at the "
                    + "shifted coefficient isolates each actual mode on each state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("state-field-residue-closure"),
                DeclarationHandle.Create(Prefix + "residue_closure"),
                H("Every integer residue is an actual state field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("The residue field is constructed for every integer r. "
                    + "Negative residues are identified with the generic divided-derivative "
                    + "normal-minus-one product, while positive residues use the explicit "
                    + "three-field cancellation. Finite telescoping proves covariance and "
                    + "creation supplies the initial state. Relative vacuum uniqueness then "
                    + "identifies the field with Y of the actual mode product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("state-field-all-integer-iterate"),
                DeclarationHandle.Create(Prefix + "stateField_iterate_of_creation_translation_locality"),
                H("Finite two-sum iterate identity for all integer modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every actual a, b, c and every integers r and n, "
                    + "both binomial mode sums have finite support. Their difference is "
                    + "the n-mode of the actual state field Y(a_r b), with the exact "
                    + "integer Ring.choose coefficients and the factor (-1)^r. This is "
                    + "the unrestricted native iterate prerequisite for later collision "
                    + "arguments; it does not claim a Moonshine realization, equality, "
                    + "or completion of Conjecture 14.4."))),
                DescribeRole.Theorem))));
}
