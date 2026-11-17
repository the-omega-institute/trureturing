using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class NormalizedSingularHermitianKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.";
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized singular Hermitian kernels reduce to a common vector, a neutral plane, or an i-skew primitive form.", H("Normalized singular Hermitian kernel geometry"), Blocks(
            Paragraph(Text("All matrices below have type M = Matrix (Fin 3) (Fin 3) ℂ. The coordinate layer keeps real diagonal entries, conjugate-symmetric off-diagonal entries, the determinant pencil, the shear and final unitary congruences, and the complete vector, neutral-plane, and primitive alternatives.")),
            Node("M", "The three-by-three matrix type", "M is the abbreviation Matrix (Fin 3) (Fin 3) ℂ.", DescribeRole.Definition),
            Node("D", "The signature matrix", "D is the matrix with diagonal entries 1, -1, 0 and all off-diagonal entries zero.", DescribeRole.Definition),
            Node("hermitianMatrix", "Hermitian coordinate matrix", "For a,b : ℝ and z,u,v : ℂ, hermitianMatrix a b z u v is the matrix with rows [(a,z,u), (conj z,b,v), (conj u,conj v,0)], with real numbers coerced to ℂ.", DescribeRole.Definition),
            Node("shear", "The shear matrix", "For p : ℂ, shear p is the lower triangular matrix [[1,0,0],[0,1,0],[0,-p,1]].", DescribeRole.Definition),
            Node("finalUnitary", "The final unitary matrix", "finalUnitary is the displayed 3-by-3 matrix built from Real.sqrt 2, its inverse, and Complex.I: rows [(r⁻¹,I*r⁻¹,0),(r⁻¹,-I*r⁻¹,0),(0,0,I)] with r = sqrt 2.", DescribeRole.Definition),
            Node("iSkew3", "The i-skew set", "iSkew3 is the set of matrices ∃ x y z : ℝ, A = I • [[0,x,y],[-x,0,z],[-y,-z,0]] after coercion to ℂ.", DescribeRole.Definition),
            Node("e3", "The third coordinate vector", "e3 : Fin 3 → ℂ is ![0,0,1].", DescribeRole.Definition),
            Node("hermitian_coordinates", "Coordinates of every Hermitian matrix", "For every H : M with H.IsHermitian, there exist a,b,c : ℝ and z,u,v : ℂ such that H = [[a,z,u],[conj z,b,v],[conj u,conj v,c]] with real entries coerced to ℂ.", DescribeRole.Theorem),
            Node("determinant_pencil_general", "The general determinant pencil", "For all a,b,c,t : ℝ and z,u,v : ℂ, det(D + (t : ℂ) • [[a,z,u],[conj z,b,v],[conj u,conj v,c]]) equals -(t:ℂ)*(c:ℂ) + (t:ℂ)^2*((b:ℂ)*(c:ℂ)-(a:ℂ)*(c:ℂ)+conj u*u-conj v*v) + (t:ℂ)^3*((a:ℂ)*(b:ℂ)*(c:ℂ)-(a:ℂ)*(conj v*v)-(b:ℂ)*(conj u*u)+z*v*conj u+conj z*conj v*u-(c:ℂ)*(z*conj z)).", DescribeRole.Theorem),
            Node("hermitianMatrix_det", "The coordinate determinant", "For all a,b : ℝ and z,u,v : ℂ, det(hermitianMatrix a b z u v) = -(a:ℂ)*(conj v*v) - (b:ℂ)*(conj u*u) + z*v*conj u + conj z*conj v*u.", DescribeRole.Theorem),
            Node("shear_identity", "The shear congruence identity", "For a,b : ℝ and p,u : ℂ satisfying (a+b : ℂ) = conj p*u + p*conj u, shear pᴴ * hermitianMatrix a b (p*u) u (conj u) * shear p = [[a,0,u],[0,-a,conj u],[conj u,u,0]].", DescribeRole.Theorem),
            Node("final_unitary_identity", "The final unitary identity", "For a,x,y : ℝ, finalUnitaryᴴ * [[a,0,x+I*y],[0,-a,x-I*y],[x-I*y,x+I*y,0]] * finalUnitary = I • [[0,a,sqrt 2*x],[-a,0,sqrt 2*y],[-sqrt 2*x,-sqrt 2*y,0]], with real entries coerced to ℂ.", DescribeRole.Theorem),
            Node("finalUnitary_isUnit", "The final unitary is invertible", "IsUnit (finalUnitary : M).", DescribeRole.Theorem),
            Node("zero_graph_common_kernel", "The zero graph gives a common kernel", "For K : Submodule ℝ M, if ∀ H ∈ K, H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0, then ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0.", DescribeRole.Theorem),
            Node("universal_coefficient_constraints", "Universal coefficient constraints", "For K : Submodule ℝ M with D ∈ K, every H ∈ K Hermitian, and det H = 0 for every H ∈ K, one has ∀ H ∈ K, H 2 2 = 0 ∧ conj(H 0 2)*H 0 2 = conj(H 1 2)*H 1 2.", DescribeRole.Theorem),
            Node("universal_faithful_coordinate_representation", "Faithful singular coordinates", "Under the same K, D, Hermitian, and singular hypotheses, every H ∈ K has ∃ a b : ℝ, ∃ z u v : ℂ, H = hermitianMatrix a b z u v ∧ conj u*u = conj v*v ∧ ((a+b : ℝ) : ℂ)*(conj u*u) = z*v*conj u + conj z*conj v*u.", DescribeRole.Theorem),
            Node("universal_common_graph_orientation", "A common graph orientation", "Under the same K, D, Hermitian, and singular hypotheses, ∃ c : ℂ, ‖c‖ = 1 ∧ ((∀ H ∈ K, H 1 2 = c * H 0 2) ∨ (∀ H ∈ K, H 1 2 = c * conj(H 0 2))).", DescribeRole.Theorem),
            Node("linear_graph_common_kernel_or_neutral_plane", "The linear graph alternative", "For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, and hgraph : ∀ H ∈ K, H 1 2 = c*H 0 2, either ∃ v ≠ 0 with ∀ H ∈ K, H*ᵥv=0, or ∃ W : Submodule ℂ (Fin 3 → ℂ), finrank ℂ W = 2 and ∀ H ∈ K, ∀ w,w' ∈ W, star w ⬝ᵥ (H*ᵥw')=0.", DescribeRole.Theorem),
            Node("conjugate_graph_proper_image_common_kernel_or_neutral_plane", "The proper conjugate graph alternative", "For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, hgraph : ∀ H ∈ K, H 1 2 = c*conj(H 0 2), and hnotonto : ¬∀ u : ℂ, ∃ H ∈ K, H 0 2 = u, the same common-vector or finrank-two neutral-plane disjunction holds.", DescribeRole.Theorem),
            Node("normalizedGraphTrichotomy", "The normalized graph trichotomy", "normalizedGraphTrichotomy is the proved proposition ∀ K : Submodule ℝ M, D ∈ K → (∀ H ∈ K, H.IsHermitian) → (∀ H ∈ K, H.det = 0) → (∃ v ≠ 0, ∀ H ∈ K, H*ᵥv=0) ∨ (∃ W, finrank ℂ W=2 ∧ ∀ H ∈ K, ∀ w,w'∈W, star w ⬝ᵥ(H*ᵥw')=0) ∨ (∃ C : M, IsUnit C ∧ ∀ H, H ∈ K ↔ Cᴴ*H*C ∈ iSkew3). Its proposition follows by combining the common graph orientation with the linear, proper conjugate, and surjective conjugate alternatives; NativeThreeKernelGeometry establishes this trichotomy and then excludes the primitive alternative for native compressions.", DescribeRole.Definition),
            Node("surjective_conjugate_graph_primitive", "The surjective conjugate primitive", "For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, hgraph : ∀ H ∈ K, H 1 2 = c*conj(H 0 2), and honto : ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u, there exists C : M with IsUnit C and ∀ H : M, H ∈ K ↔ Cᴴ * H * C ∈ (iSkew3 : Set M)." , DescribeRole.Theorem))));
}
