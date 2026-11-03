using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ThetaChargeRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charge rotations and lattice reflection give an exact dihedral invariant-dimension formula.",
        H("Charge Rotation and Dihedral Invariants"),
        Blocks(
            Paragraph(Text(
                "An additive charge map ell to ZMod 3 and a unit-valued phase define charge rotations on every energy grade. Lattice theta conjugates each rotation to its inverse, giving an action of the six-element dihedral group. No surjectivity of ell is assumed.")),
            Law("gradeChargeResidue_finrank", "Residue-sector dimension",
                "For a positive-definite lattice, the dimension of charge residue r at integer energy n is the number of energy-fiber basis labels with ell(charge) = r."),
            Law("gradeTheta_mem_gradeChargeResidue_neg", "Reflection reverses charge residue",
                "On every energy grade of a positive-definite lattice, theta maps residue r into residue -r."),
            Law("gradeChargeRotation_trace_sum", "Rotation trace sum",
                "For a nontrivial phase and a positive-definite lattice, the sum of the three rotation traces is three times the number N0 of neutral-residue energy-fiber labels."),
            Law("gradeChargeDihedral_character_reflection", "Reflection characters",
                "Each of the three dihedral reflections has character equal to the trace T of theta on the full energy grade. This identity requires neither positive definiteness nor a nontrivial phase."),
            Law("gradeChargeDihedral_character_average_sharp", "Exact character average",
                "For a positive-definite lattice and a nontrivial phase, one sixth of the sum of the six dihedral characters is (N0 + T)/2. The trace T is on the full energy grade."),
            Law("gradeChargeDihedral_invariants_finrank_sharp", "Exact invariant dimension",
                "Under the same hypotheses, the complex dimension of the dihedral invariant submodule is (N0 + T)/2. This is a finite-grade representation-theoretic consequence; no analytic convergence or literature novelty is asserted.")),
        []));

    private static DocumentBlock Law(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("theta-charge-rotation-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
