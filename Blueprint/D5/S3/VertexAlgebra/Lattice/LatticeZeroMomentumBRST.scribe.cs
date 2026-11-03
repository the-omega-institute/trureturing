using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeZeroMomentumBRSTDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("latticezeromomentumbrst-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original zero-momentum relative shell and its actual operators",
        H("The original zero-momentum relative shell and its actual operators"), Blocks(
            Paragraph(Text("Let D : LatticeData have arbitrary natural rank, including zero, and let H be a complex matrix indexed by Fin D.rank. The operator and shell-basis results state both equations H * gramComplex D = 1 and gramComplex D * H = 1 explicitly. No signature, positive form, distinguished null frame, nonzero light-cone component or rank 26 condition is imposed.")),
            Paragraph(Text("State D is the original all-charge Carrier D tensor the countable occupation Fock space. The shell is literally fixedMomentum D 0 intersect ker(ghostB D 0) intersect ker(totalL0 D H), where totalL0 is the unshifted original matter-plus-ghost zero mode. Its original labels satisfy oscillatorEnergy d + relativeEnergy S = 1 and exclude ghost site 3. relativeEnergy S = energy S + 1 rewrites this original equation; it does not change the operator or add an intercept.")),
            Paragraph(Text("The actual site energies force every allowed low occupation into {1,5}: even sites have energy at least two, and every odd site other than 1,3,5 has energy at least two. Site 1 has energy minus one, site 3 is excluded by b(0), and site 5 has energy one. Thus relative energy zero has exactly occupation {1}, while relative energy one has exactly the empty occupation and {1,5}. Oscillator energy one has exactly one original frequency-zero current. These exhaust all original zero-shell labels.")),
            Paragraph(Text("Write g for the existing neutral ground and J_i for the existing currentState. The original shell basis consists of g tensor ket empty, J_i tensor ket {1} for every i, and g tensor ket {1,5}. Its actual basis representation gives shellEquiv with coefficient space Complex x ((Fin D.rank -> Complex) x Complex). Its inverse followed by the original inclusion is Psi(A,v,C) = A*(g tensor ket empty) + (sum_i v(i)*J_i) tensor ket {1} + C*(g tensor ket {1,5}). Surjectivity concerns the entire literal original shell.")),
            Paragraph(Text("The original charge is exactly LatticeBRST.totalCharge = T + ghostCharge with the original cubic Qg. For odd occupations the pure-c Ward sum at integer r is captured on the finite interval [r-1,1]; outside this interval one c-mode annihilates the occupation, directly or after CAR. The actual cubic action on ket {1} is -c(0) ket {1}. The actual matter sum on J_i tensor ket {1} retains exactly its m=0 term J_i tensor c(0) ket {1}, so these two original terms cancel. The original ground and two-ghost basis branches are also annihilated. Exhaustion then proves totalCharge x = 0 for every literal zero-shell state, without assuming nilpotence.")),
            Paragraph(Text("The number operator is the existing LatticeMatterGhostDegree.tensorNumber, the identity on matter tensored with BcGhostCharge.ghostNumber. It is actual signed occupation charge and has basis eigenvalues 0,1,2. Hence its coordinate action is (A,v,C) -> (0,v,2*C). This is neither a longitudinal filtration nor a shifted degree.")),
            Paragraph(Text("The original carrier and operators retain their repository supplier definitions. Basis reindexing and finite coordinate equivalences reuse Mathlib under Apache 2.0. The conclusions are algebraic prerequisites. They assert no cohomology computation, positivity, no-ghost theorem, Monster or moonshine construction, full VOA/CFT or string model, or AdS/CFT correspondence.")),
            Node("relativeEnergy_empty", "The empty original occupation has relative energy one.", DescribeRole.Theorem),
            Node("relativeEnergy_down", "The original occupation {1} has relative energy zero.", DescribeRole.Theorem),
            Node("relativeEnergy_top", "The original occupation {1,5} has relative energy one.", DescribeRole.Theorem),
            Node("ghost_level_zero_iff", "For every finite occupation S excluding site 3, relativeEnergy S = 0 if and only if S = {1}.", DescribeRole.Theorem),
            Node("ghost_level_one_iff", "For every finite occupation S excluding site 3, relativeEnergy S = 1 if and only if S is empty or {1,5}.", DescribeRole.Theorem),
            Node("oscillatorEnergy_one_iff", "For every lattice datum D and original exponent d, oscillatorEnergy d = 1 if and only if d is single (i,0) 1 for some i : Fin D.rank.", DescribeRole.Theorem),
            Node("ZeroIndex", "The index type Unit + (Fin D.rank + Unit) includes both scalar states and every original current, including when rank is zero.", DescribeRole.Definition),
            Node("zeroLabel", "The labels are ((0,0),empty), ((0,single (i,0) 1),{1}) and ((0,0),{1,5}) in the original tensor label type.", DescribeRole.Definition),
            Node("allowed_zero_iff", "For every original tensor label l, l belongs to allowedLabels D 0 if and only if l is zeroLabel D k for an index k. This proves exhaustion.", DescribeRole.Theorem),
            Node("zeroIndexEquiv", "Injectivity of the displayed labels and their exhaustion give an equivalence with the original ShellIndex D 0.", DescribeRole.Definition),
            Node("ground", "This abbreviation refers to the existing original charge-zero vacuum in LatticeAllStateField.", DescribeRole.Definition),
            Node("current", "This abbreviation refers to the existing currentState of LatticeActualConformalState; its original oscillator frequency is zero and its energy is one.", DescribeRole.Definition),
            Node("zeroVector", "Each index gives its original matter vector tensored with the displayed occupation ket.", DescribeRole.Definition),
            Node("zeroBasis", "Under both inverse-Gram equations, reindexing the original shellBasis gives a basis of the literal original zero-momentum relative shell.", DescribeRole.Definition),
            Node("zeroBasis_coe", "For every basis index, coercion into the original tensor carrier gives exactly zeroVector D k.", DescribeRole.Theorem),
            Node("Coordinates", "The coefficient space is Complex x ((Fin D.rank -> Complex) x Complex).", DescribeRole.Definition),
            Node("shellEquiv", "The basis representation and the splitting of its finite index give a linear equivalence from the entire original shell to Coordinates D.", DescribeRole.Definition),
            Node("Psi", "The inverse coordinate equivalence followed by the original submodule inclusion maps coordinates into the original State D.", DescribeRole.Definition),
            Node("Psi_formula", "For every coordinate tuple (A,v,C), Psi is A times the original vacuum tensor ket empty, plus the sum of v(i) times the original currents tensor ket {1}, plus C times the original vacuum tensor ket {1,5}. Both inverse-Gram equations are explicit.", DescribeRole.Theorem),
            Node("Qg_down", "The original cubic charge on ket {1} is minus c(0) applied to ket {1}. The full Ward sum is evaluated using its all-integer annihilation tail and CAR.", DescribeRole.Theorem),
            Node("c_minus_one_down", "The actual occupation creation phase gives c(-1) ket {1} = -ket {1,5}.", DescribeRole.Theorem),
            Node("Qg_top", "The original cubic charge annihilates ket {1,5}; the c(-1) Ward identity and the actual occupation phase determine the cancellation.", DescribeRole.Theorem),
            Node("sugawara_ground", "For every D, every complex rank-indexed matrix H, and every integer m >= -1, the actual Sugawara mode kills the original neutral ground. Positive and zero modes use the existing charged-ground formulas; the minus-one mode has vanishing neutral contractions.", DescribeRole.Theorem),
            Node("T_current_down", "Under both inverse-Gram equations, the full matter coupling on current(i) tensor ket {1} is current(i) tensor c(0) ket {1}. Every summation index other than zero is proved to vanish.", DescribeRole.Theorem),
            Node("totalCharge_zeroVector", "Under both inverse-Gram equations, the actual totalCharge annihilates every displayed basis vector. On the current branch the actual matter zero term cancels the original cubic term.", DescribeRole.Theorem),
            Node("totalCharge_on_zero_shell", "For every original tensor state x in the literal unshifted zero-momentum relative shell, totalCharge D H x = 0 under the two inverse-Gram equations. Basis exhaustion supplies the arbitrary-state conclusion.", DescribeRole.Theorem),
            Node("shellGhostDegree", "The three branches have degrees zero, one and two respectively. These are actual signed occupation numbers on the allowed occupations.", DescribeRole.Definition),
            Node("totalGhostNumber_zeroVector", "The existing tensorNumber acts on each original zeroVector by its displayed degree, with no grading shift.", DescribeRole.Theorem),
            Node("totalGhostNumber_Psi", "For all coordinates (A,v,C), the existing actual tensorNumber sends Psi(A,v,C) to Psi(0,v,2*C), under both inverse-Gram equations.", DescribeRole.Theorem))));
}
