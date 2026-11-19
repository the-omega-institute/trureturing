using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class OriginalOrbifoldRelativeNullDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull";

    private static DocumentBlock Node(
        string name, string heading, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(
            DescribeId.Create("original-orbifold-relative-null-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(paragraph => Paragraph(Text(paragraph))).ToArray()), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native relative BRST complex at integral null momentum",
        H("Native relative BRST exactness at nonzero null momentum"),
        Blocks(
            Paragraph(Text("Use the actual Golay–Leech orbifold of central charge 24 and the ordered hyperbolic lattice of central charge 2 as matter. The state space tensors that matter with the native bc occupation Fock space. For an integral charge a = (a₀, a₁), the ordered Gram matrix has off-diagonal entries 1 and diagonal entries 0, so the charge half-norm is a₀a₁. The relative mass shell at a is the intersection of the fixed-charge space with the kernels of b₀ and total L₀. Its d is the restriction of the original Q. Charge preservation, the b₀ Ward identity, and commutation with total L₀ make that restriction well-defined. The critical-matter square identity gives d² = 0.")),
            Node("levelOccupationSets_zero", "Relative ghost level zero", DescribeRole.Theorem,
                "The level-zero occupation set contains only {1}. The relative condition excludes site 3, the c₀ site."),
            Node("levelOccupationSets_one", "Relative ghost level one", DescribeRole.Theorem,
                "The level-one occupations are ∅ and {1, 5}."),
            Node("allowedLabels_iff", "Complete null-shell labels", DescribeRole.Theorem,
                "At half-norm zero the orbifold weight, hyperbolic oscillator energy and relative ghost level must sum to 1. The actual orbifold has no weight-one states and its weight-zero line is the vacuum line. Thus either there is exactly one first-frequency hyperbolic oscillator with occupation {1}, or there are no oscillators and the ghost occupation is ∅ or {1, 5}. In all cases the momentum is the original a."),
            Node("shellVector", "Literal tensor representatives", DescribeRole.Definition,
                "At fixed charge a, write B for the actual orbifold vacuum tensored with the charged oscillator monomial 1 and the empty ghost ket. Write Mᵢ for the same vacuum with charged monomial X(i,0) and ket {1}, where i is 0 or 1. Write T for the vacuum with charged monomial 1 and ket {1, 5}. The polynomial index 0 is frequency one."),
            Node("shellBasis", "Basis of the actual relative mass shell", DescribeRole.Definition,
                "The shell basis restricts the ambient basis to the allowed labels and normalizes the common nonzero vacuum scalar. The order is B, M₀, M₁, T."),
            Node("shellBasis_coe", "Basis tensors in the original carrier", DescribeRole.Theorem,
                "Under the inclusion of the relative mass shell into the state space, each basis vector is the corresponding literal tensor representative."),
            Node("shell_finrank", "Four-dimensional null shell", DescribeRole.Theorem,
                "The complex dimension is 4 at every integral zero-half-norm charge."),
            Node("ghostNumber", "Shell ghost numbers", DescribeRole.Definition,
                "The basis labels B, M₀, M₁, T have ghost numbers 0, 1, 1, 2 respectively."),
            Node("ghostNumber_shellVector", "Native grading on the tensors", DescribeRole.Theorem,
                "The original lifted ghost-number operator acts on each literal tensor by its designated ghost number."),
            Paragraph(Text("On these tensors Q is the statewise finite sum of Lₘ ⊗ c(−m) plus the native cubic ghost term Qg acting on the ghost factor. For m ≥ −1 the orbifold mode kills the vacuum by translation at m = −1 and creativity at m ≥ 0. For m < −1 the ghost mode annihilates each of the three occupations. The remaining matter modes therefore act through the actual hyperbolic Sugawara operators.")),
            Node("Q_bottom", "Native action on the bottom tensor", DescribeRole.Theorem,
                "Qg kills the empty ket. Hyperbolic L₀ gives the half-norm, which vanishes, and all positive modes kill the charged ground monomial. At m = −1 the Sugawara mode creates the current with coefficients (a₀, a₁), and c(1) takes the empty ket to ket {1} with sign +1. Thus Q B = a₀ M₀ + a₁ M₁."),
            Node("Q_middle", "Native action on the one-oscillator tensors", DescribeRole.Theorem,
                "At m = −1, c(1) repeats the occupied site 1 and vanishes. At m = 0 the matter eigenvalue is 1 and the contribution with c(0) cancels Qg on ket {1}. For m > 0, the Sugawara–current commutator reduces the matter action to current mode m−1 on the charged ground. This vanishes for m > 1. At m = 1 the current zero mode gives the Gram pairing of the i-th ordered basis vector with a, namely a₁ for i = 0 and a₀ for i = 1. The native occupation sign is c(−1) ket {1} = −ket {1, 5}, so Q M₀ = −a₁ T and Q M₁ = −a₀ T."),
            Node("Q_top", "Native action on the top tensor", DescribeRole.Theorem,
                "Qg kills ket {1, 5}. The m = −1 term repeats site 1, L₀ kills the null charged ground, and positive matter modes kill that ground. Thus Q T = 0."),
            Node("differential_on_basis", "The three graded maps", DescribeRole.Theorem,
                "In the ordered basis the maps in ghost degrees 0, 1 and 2 are t ↦ (a₀t, a₁t), (v₀, v₁) ↦ −a₁v₀ − a₀v₁, and the zero map. The basis inclusions identify these maps with Q on the actual tensors. These formulas also hold at a = 0."),
            Node("coordinateDifferential", "Explicit differential in four coordinates", DescribeRole.Definition,
                "Write a vector as (t, v₀, v₁, w) in the order B, M₀, M₁, T. The differential sends it to (0, a₀t, a₁t, −a₁v₀ − a₀v₁)."),
            Node("coordinateHomotopy", "Explicit degree-lowering homotopy", DescribeRole.Definition,
                "In the same order, h sends (t, v₀, v₁, w) to (a₀⁻¹v₀ + a₁⁻¹v₁, −a₁⁻¹w, −a₀⁻¹w, 0). The inverse of zero in ℂ is zero."),
            Node("coordinateDifferential_squared", "Square zero on the null axes", DescribeRole.Theorem,
                "The only possible entry of the square is the top coordinate −2a₀a₁t. It vanishes for every integral charge on either null axis."),
            Node("coordinateHomotopy_contracts", "Contraction in coordinates", DescribeRole.Theorem,
                "For a nonzero integral null charge, exactly one of a₀ and a₁ is nonzero. Its product with its inverse is 1, giving dh + hd = 1 on all four coordinates."),
            Node("coordinateDifferential_exact", "Range equals kernel in coordinates", DescribeRole.Theorem,
                "The square-zero identity puts the range in the kernel. For a closed vector x the homotopy gives x = d(hx), proving the reverse inclusion."),
            Node("shellCoordinates", "Linear equivalence given by the shell basis", DescribeRole.Definition,
                "The equivalence sends each native basis vector to its coordinate unit vector."),
            Node("differential_conjugate", "Conjugacy with the native differential", DescribeRole.Theorem,
                "Taking shell coordinates after applying the restricted Q agrees with applying the explicit differential after taking shell coordinates. This equality holds at every integral null charge, including zero."),
            Node("exists_contraction", "Contraction on either nonzero null axis", DescribeRole.Theorem,
                "For a ≠ 0 with a₀a₁ = 0, take j to be the sole index with aⱼ ≠ 0 and k the other index. Define h(Mⱼ) = B/aⱼ and h(T) = −Mₖ/aⱼ, with h(B) = h(Mₖ) = 0. Extend complex-linearly. On B and Mₖ the term hd is the identity. On Mⱼ and T the term dh is the identity. This proves dh + hd = 1 on the relative mass shell."),
            Node("differential_exact", "Vanishing relative cohomology at nonzero null charge", DescribeRole.Theorem,
                "For every integral a with chargeEnergy hyperbolicData a = 0 and a ≠ 0, Lean proves LinearMap.range (differential a) = LinearMap.ker (differential a). The shell-coordinate equivalence transports the equality of range and kernel to the restricted native operator. At a = 0 the same four-dimensional shell has d = 0, so its kernel is the entire shell and its range is zero. Exactness here concerns the native relative complex of this particular orbifold and hyperbolic plane at nonzero null charge."),
            Paragraph(Text("The shell calculation and contraction are repository derivations from the original lattice, orbifold and occupation-ghost operators. The Virasoro BRST construction supplies the mode conventions and Ward identities.")))));
}
