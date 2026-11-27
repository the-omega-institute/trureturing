using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qOrderThreeLiftRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeLiftRigidity.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjectivity of the integral cyclic norm forces every mode-preserving cube-one lift of the Nebe order-three action to fix its fixed-charge ground states.",
        H("Fixed-Charge Rigidity for the P48q Order-Three Lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cycle-norm-trivial-fixed-phase"),
                DeclarationHandle.Create(Prefix + "fixed_charge_phase_eq_one_of_cube_one_norm_image"),
                H("The phase on a cyclic norm is trivial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let g be a cube-one isometry of an even integral lattice. Suppose every fixed charge is the sum of an orbit x, gx, g²x. Consider a complex-linear cube-one lift U that preserves the integer vertex modes and acts on each charged ground state by U(eₐ) = η(a)e₍gₐ₎.")),
                    Paragraph(Text("Preserving the normalized ground product relates η(a+b) to η(a)η(b) by the ratio of the two cocycle signs. Apply this relation twice to the three orbit charges. Rotating the cocycle product past x introduces two equal skew signs, since the pairings of x with gx and g²x agree. The signs multiply to one. The cube identity makes η(x)η(gx)η(g²x) equal to one, which forces η(x+gx+g²x) to equal one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-fixed-phase"),
                DeclarationHandle.Create(Prefix + "p48q_order_three_lift_standard"),
                H("Every such P48q lift fixes the fixed-charge ground states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("Right multiplication by the concrete Nebe matrix is the order-three additive isometry of the catalogue lattice. The integral norm certificate supplies an orbit-sum preimage for every fixed row. Applying the general cyclic norm argument proves that the phase of every mode-preserving cube-one monomial lift equals one on all fixed charges."))),
                DescribeRole.Theorem))));
}
