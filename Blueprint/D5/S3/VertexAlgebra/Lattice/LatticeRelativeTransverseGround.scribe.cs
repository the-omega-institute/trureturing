using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;
internal sealed class LatticeRelativeTransverseGroundDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string telescope, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticeoriginalground-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeRelativeTransverseGround." + name),
        H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("Exact Lean statement in the parameter context below: " + telescope))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original transverse polynomial energy and relative shell",
        H("Original transverse polynomial energy and relative shell"), Blocks(
        Paragraph(Text("The original state space is Carrier D tensor[Complex] the actual algebraic bc Fock space, with every integral charge retained. D is arbitrary LatticeData and F is its actual null frame. For any natural t, B is any complex basis indexed by Fin t of the actual transverse space F.K. B need not be real or orthonormal. H satisfies both inverse-Gram equations H gramComplex D = 1 and gramComplex D H = 1 wherever the original Sugawara zero mode is used. totalL0 is exactly matterMode D H 0 + ghostVirasoro D 0, without an identity shift.")),
        Paragraph(Text("The energy-preservation statements quantify independent integral charges p and q, including zero. Their original Ward, tensor cancellation, locally finite sums and inverse-count functional-calculus proofs are used in the literal shellD0 and shellH maps. P0 stability uses the original number spectrum and the same unshifted energy commutation; its b0 law is the existing original contraction law. No desired stability or energy certificate is a premise.")),
        Paragraph(Text("The independent polynomial space has variables Fin t times Nat. weight nu is the sum of nu(j,r) times r+1. energyTarget consists exactly of polynomials whose coefficients vanish unless weight nu + chargeEnergy D p = 1 in Int. target is its image under the existing actual groundMap F B p. These definitions mention neither P0 nor relativeMassShell. The ground ghost vector is the original ket {1}, with unshifted ghost energy -1. Ground coefficient recovery uses the original actualBasis and the injective transverse exponent map.")),
        Paragraph(Text("The homogeneous substitution theorem for the actual null-frame coordinate equivalence, the frozen Sugawara weighted-homogeneous theorem and the actual ghost zero-mode theorem give the exact ground-map energy formula. Linear extension gives its all-polynomial intertwining. Its zero kernel is the independent integer coefficient target. The frozen literal_relative_ground theorem then identifies this genuine image with relativeMassShell D H p intersect ker M. This is an algebraic application of those frozen suppliers; no literature novelty is claimed.")),
        Paragraph(Text("Inclusion is the literal subtype inclusion into the same relativeMassShell. Projection applies the original P0 and restricts its codomain using the proved image identification. shellD0 and shellH are the original d0 and h restricted using the actual preservation proofs. Their retraction and side identities reuse the original ambient contraction, square and zero-product laws. Only shell_contraction assumes pPlus p is nonzero. The polynomial target, its identification, stability and the empty shell theorem have no such assumption. If chargeEnergy D p exceeds one, the existing relativeMassShell_eq_bot_of_one_lt supplies the empty original shell; no zero cutoff is substituted for that result.")),
        Paragraph(Text("These statements do not assert full-Q perturbation, transferred cohomology, Hermitian descent, no-ghost positivity, Monster moonshine, a full VOA/CFT construction, anomaly or fusion completeness, string theory or AdS/CFT. The two retained energy source-family attempts remain unfinished under https://github.com/the-omega-institute/trureturing/issues/25847 and do not establish exact source selection or whole-source reconstruction. No registration has been completed for the additional ground and shell statements, and no declared_validated audit is claimed for them.")),
        Node("d0_preserves_original_relative_constraints", "theorem d0_preserves_original_relative_constraints (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p q : Charge D) (x : State D) (hxCharge : chargeProject p x = x) (hxB0 : ghostB0 (D", DescribeRole.Theorem),
        Node("h_preserves_original_relative_constraints", "theorem h_preserves_original_relative_constraints (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p q : Charge D) (x : State D) (hxCharge : chargeProject p x = x) (hxB0 : ghostB0 (D", DescribeRole.Theorem),
        Node("Polynomial", "abbrev Polynomial (t : ℕ)", DescribeRole.Definition),
        Node("Exponent", "abbrev Exponent (t : ℕ)", DescribeRole.Definition),
        Node("weight", "def weight {t : ℕ} (nu : Exponent t) : ℕ", DescribeRole.Definition),
        Node("energyTarget", "def energyTarget (D : LatticeData) (t : ℕ) (p : Charge D) : Submodule ℂ (Polynomial t)", DescribeRole.Definition),
        Node("target", "def target (p : Charge D) : Submodule ℂ (State D)", DescribeRole.Definition),
        Node("groundIndex", "def groundIndex (p : Charge D) (nu : Exponent t) : StateIndex D t", DescribeRole.Definition),
        Node("groundIndex_injective", "theorem groundIndex_injective (p : Charge D) : Function.Injective (groundIndex (t", DescribeRole.Theorem),
        Node("groundMap_coefficient", "theorem groundMap_coefficient (p : Charge D) (f : Polynomial t) (nu : Exponent t) : (actualBasis F B).repr (groundMap F B p f) (groundIndex p nu) = f.coeff nu", DescribeRole.Theorem),
        Node("groundMap_injective", "theorem groundMap_injective (p : Charge D) : Function.Injective (groundMap F B p)", DescribeRole.Theorem),
        Node("energyOperator", "def energyOperator (p : Charge D) : Module.End ℂ (Polynomial t)", DescribeRole.Definition),
        Node("energyOperator_coefficient", "theorem energyOperator_coefficient (p : Charge D) (f : Polynomial t) (nu : Exponent t) : (energyOperator p f).coeff nu = (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) * f.coeff nu", DescribeRole.Theorem),
        Node("energyOperator_monomial", "theorem energyOperator_monomial (p : Charge D) (nu : Exponent t) : energyOperator p (monomial nu 1) = (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) • monomial nu 1", DescribeRole.Theorem),
        Node("energyOperator_zero_iff", "theorem energyOperator_zero_iff (p : Charge D) (f : Polynomial t) : energyOperator p f = 0 ↔ f ∈ energyTarget D t p", DescribeRole.Theorem),
        Node("frequencyWeight_mapDomain", "theorem frequencyWeight_mapDomain (nu : Exponent t) : Finsupp.weight frequencyWeight (nu.mapDomain transverseVariable) = weight nu", DescribeRole.Theorem),
        Node("ghost_ground_energy", "theorem ghost_ground_energy : GRE.energy ({1} : Finset ℕ) = -1", DescribeRole.Theorem),
        Node("totalL0_groundMap_monomial", "theorem totalL0_groundMap_monomial (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (nu : Exponent t) : totalL0 D H (groundMap F B p (monomial nu 1)) = (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) • groundMap F B p (monomial nu 1)", DescribeRole.Theorem),
        Node("totalL0_groundMap", "theorem totalL0_groundMap (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) : (totalL0 D H).comp (groundMap F B p) = (groundMap F B p).comp (energyOperator p)", DescribeRole.Theorem),
        Node("groundMap_mem_shell_iff", "theorem groundMap_mem_shell_iff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (f : Polynomial t) : groundMap F B p f ∈ relativeMassShell D H p ↔ f ∈ energyTarget D t p", DescribeRole.Theorem),
        Node("target_eq_shell_inf_ker", "theorem target_eq_shell_inf_ker (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) : target F B p = relativeMassShell D H p ⊓ LinearMap.ker (M F)", DescribeRole.Theorem),
        Node("target_projection_fix", "theorem target_projection_fix (p : Charge D) (u : target F B p) : P0 F B u = u", DescribeRole.Theorem),
        Node("inclusion", "def inclusion : target F B p →ₗ[ℂ] relativeMassShell D H p", DescribeRole.Definition),
        Node("shellP0", "def shellP0 : Module.End ℂ (relativeMassShell D H p)", DescribeRole.Definition),
        Node("shellD0", "def shellD0 : Module.End ℂ (relativeMassShell D H p)", DescribeRole.Definition),
        Node("shellH", "def shellH : Module.End ℂ (relativeMassShell D H p)", DescribeRole.Definition),
        Node("projection", "def projection : relativeMassShell D H p →ₗ[ℂ] target F B p", DescribeRole.Definition),
        Node("projection_inclusion", "theorem projection_inclusion : (projection F B H hHG hGH p).comp (inclusion F B H hHG hGH p) = LinearMap.id", DescribeRole.Theorem),
        Node("inclusion_projection", "theorem inclusion_projection : (inclusion F B H hHG hGH p).comp (projection F B H hHG hGH p) = shellP0 F B H hHG hGH p", DescribeRole.Theorem),
        Node("shell_d0_square", "theorem shell_d0_square : shellD0 F H hHG hGH p * shellD0 F H hHG hGH p = 0", DescribeRole.Theorem),
        Node("shell_d0_inclusion", "theorem shell_d0_inclusion : (shellD0 F H hHG hGH p).comp (inclusion F B H hHG hGH p) = 0", DescribeRole.Theorem),
        Node("projection_shell_d0", "theorem projection_shell_d0 : (projection F B H hHG hGH p).comp (shellD0 F H hHG hGH p) = 0", DescribeRole.Theorem),
        Node("shell_contraction", "theorem shell_contraction (hp : F.pPlus p ≠ 0) : shellD0 F H hHG hGH p * shellH F B H hHG hGH p + shellH F B H hHG hGH p * shellD0 F H hHG hGH p = 1 - (inclusion F B H hHG hGH p).comp (projection F B H hHG hGH p)", DescribeRole.Theorem),
        Node("shell_h_square", "theorem shell_h_square : shellH F B H hHG hGH p * shellH F B H hHG hGH p = 0", DescribeRole.Theorem),
        Node("shell_h_inclusion", "theorem shell_h_inclusion : (shellH F B H hHG hGH p).comp (inclusion F B H hHG hGH p) = 0", DescribeRole.Theorem),
        Node("projection_shell_h", "theorem projection_shell_h : (projection F B H hHG hGH p).comp (shellH F B H hHG hGH p) = 0", DescribeRole.Theorem)
    )));
}
