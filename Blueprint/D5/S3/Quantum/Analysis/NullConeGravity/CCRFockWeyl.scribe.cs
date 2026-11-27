using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRFockWeylDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strongly continuous Weyl displacements and their behavior under basis change and occupation splitting.",
        H("Unitary Weyl displacements in bosonic Fock space"),
        Blocks(
            Paragraph(Text("The coherent Gram identity determines a displacement unitary from its action on "
                + "coherent vectors. Occupation splitting presents a vector as a square-summable family in "
                + "the retained modes. This presentation gives the vector families used to describe "
                + "restrictions of Gaussian states in the excitability problem of Satishchandran and Sorce.")),
            Entry("weyl-unitary", "fockWeyl", "Weyl displacement unitary",
                "Translation of the coherent input by z, together with the compensating exponential "
                + "factor, preserves the coherent Gram matrix. The resulting linear isometry extends "
                + "from the dense coherent span and maps onto Fock space.", DescribeRole.Definition),
            Entry("weyl-coherent-action", "fockWeyl_exponential", "Displacement of a coherent vector",
                "The unitary W(z) sends the coherent vector of w to exp(−‖z‖²/2 − ⟨z, w⟩) "
                + "times the coherent vector of z + w."),
            Entry("weyl-zero", "fockWeyl_zero", "Displacement at zero",
                "The displacement at zero is the identity isometric equivalence."),
            Entry("weyl-product", "fockWeyl_mul", "Weyl multiplication law",
                "With antilinear-first inner products, W(z)W(w) equals exp(−i Im⟨z, w⟩) times W(z + w) "
                + "on every vector. If ⟨kf, kg⟩ = μ(f, g) + iσ(f, g)/2, the phase is exp(−iσ(f, g)/2). "
                + "An imaginary part of −σ(f, g)/2 gives exp(+iσ(f, g)/2)."),
            Entry("weyl-inverse", "fockWeyl_symm", "Inverse displacement",
                "The inverse of W(z) is W(−z), since the inner product of z and −z is real and "
                + "their sum is zero."),
            Entry("weyl-vacuum", "fockWeyl_vacuum_inner", "Gaussian vacuum expectation",
                "The vacuum coefficient of W(z) is exp(−‖z‖²/2). The coherent Gram identity "
                + "gives inner product one between the vacuum and the coherent vector of z."),
            Entry("weyl-continuity", "fockWeyl_strongContinuous", "Strong continuity",
                "For each Fock vector, displacement depends continuously on the one-particle input. "
                + "The coherent action gives continuity on finite coherent sums, and the isometry "
                + "bound extends it to all vectors."),
            Entry("basis-change", "fockBasisChange", "Unitary change of Hilbert basis",
                "The common coherent Gram matrix extends the correspondence of coherent vectors "
                + "in two occupation models of the same one-particle space to a unitary.",
                DescribeRole.Definition),
            Entry("basis-change-coherent", "fockBasisChange_exponential", "Coherent vectors under basis change",
                "The basis-change unitary sends each coherent vector in the first occupation model "
                + "to the coherent vector of the same one-particle input in the second model."),
            Entry("basis-change-weyl", "fockBasisChange_weyl", "Basis independence of Weyl displacement",
                "The basis-change unitary intertwines the two Weyl displacements of the same input. "
                + "The coherent action gives the intertwining on a dense span."),
            Entry("sum-splitting", "fockSumSplit", "Disjoint-sum occupation splitting",
                "Each occupation on the disjoint sum splits uniquely into a left and a right occupation. "
                + "Regrouping amplitudes by right occupation is a unitary onto the square-summable "
                + "families of left Fock vectors.", DescribeRole.Definition),
            Entry("sum-splitting-coordinate", "fockSumSplit_apply", "Coordinate of a split vector",
                "The left occupation amplitude of the component at a right occupation equals the "
                + "original amplitude at the combined occupation."),
            Entry("left-particle-part", "fockOneParticleLeft", "Left one-particle component",
                "Restrict the original Hilbert coordinates to the left indices and reconstruct the "
                + "resulting vector in the left Hilbert basis.", DescribeRole.Definition),
            Entry("left-particle-coordinate", "fockOneParticleLeft_repr", "Coordinate of the left component",
                "Every coordinate in the left basis equals the corresponding left coordinate "
                + "in the original basis."),
            Entry("sum-splitting-weyl", "fockSumSplit_weyl", "Coordinatewise Weyl displacement",
                "When the right coordinates of the displacement input vanish, the split vector's "
                + "component at each right occupation is displaced by the left Weyl unitary. The "
                + "left input is reconstructed in the left Hilbert basis from the original left coordinates."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
