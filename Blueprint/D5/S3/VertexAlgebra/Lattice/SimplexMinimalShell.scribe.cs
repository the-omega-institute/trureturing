using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class SimplexMinimalShellDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer cut-energy rigidity determines the entire simplex minimal shell in arbitrary rank.",
        H("Complete Simplex Minimal Shell"),
        Blocks(
            Paragraph(Text(
                "For integer coordinates y on any finite index type of cardinality n at least two, let energy y be the ordered double sum of (y i minus y j) squared. It is twice the unordered complete-graph energy. Assume that some two coordinates differ; translations of all coordinates are allowed.")),
            Describe.Lean(
                DescribeId.Create("simplexminimalshell-complete-shell"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/SimplexMinimalShell.complete_shell"),
                H("Minimum and complete equality reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/conwaysloane1999spherepackings")),
                Blocks(Paragraph(Text(
                    "For every such finite type and integer function, energy is at least twice n minus two. Equality holds exactly when there exist an integer baseline a, a sign e equal to one or minus one, and a distinguished index p such that y i equals a plus e at p and equals a elsewhere. This includes n equal to two. Neither integer coordinates nor rank are bounded."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Choose a minimum coordinate value a and partition the indices into its level A and the nonempty complement B. Every crossing square is at least one by integrality, so energy is at least twice the product of the two cardinalities. For positive cardinalities k and l, k times l is at least k plus l minus one; equality forces k or l to equal one. At minimum energy, equality of the finite sums forces equality at every pair. A crossing difference from the minimum level is therefore exactly one, reconstructing two adjacent integer levels. The singleton side determines the sign. Conversely a signed singleton perturbation has exactly the stated energy.")),
            Paragraph(Text(
                "The statement is the classical minimum-vector geometry of the dual A-type root lattice, expressed without a Euclidean normalization convention; no mathematical novelty is claimed. Mathlib supplies finite minima, the integer absolute-value bound for a nonzero difference, finite-sum inequalities and their equality criterion. The new proof supplies the cut-energy rigidity and reconstruction. The cut-sum and singleton-energy identities are consumed normalization helpers, not independent mathematical contributions.")),
            Paragraph(Text(
                "For a charge x with r integer coordinates, adjoin a zero coordinate. Half its doubled energy equals Q_r(x), namely (r plus one) times the sum of coordinate squares minus the square of their sum. The equality reconstruction at Q_r(x) equal to r gives precisely the signed coordinate units and the two constant vectors with entries one or minus one. The added zero either is the distinguished singleton, giving a constant vector, or fixes the baseline to zero, giving a signed coordinate unit. For the actual rank-four lattice datum with Gram diagonal four and off-diagonal minus one, Q_4(x) is exactly bilinear D x x. The transient exact Lean application checks for every charge x that norm four is equivalent to membership in those ten listed vectors; it is an application of the general theorem and is not retained as a new D5 theorem.")),
            Paragraph(Text(
                "This identifies the charge support needed by the existing first-return ground-cycle fixed-space theorem. It does not supply a full fixed-space dimension, an orbit decomposition, oscillator contributions, a coherent S5 carrier action, or phases of such an action. Those require further actual-lattice constructions. No theory volume is added for this known shell result.")))));
}
