using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class ConformalGroupSO24In4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/difrancesco1997cft");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signature (2,4), Minkowski inversion, four-point cross-ratios and the real twistor Lie equivalence.",
        H("Four-dimensional conformal algebra and twistors"),
        Blocks(
            Paragraph(Text("Rotations of a signed six-dimensional form give the conformal generators. The Minkowski chart exhibits their conformal geometry through distance scaling, while the chiral Dirac matrices give a four-component complex representation.")),
            Entry("orthogonal-generator", "so24_antisym_metric", "Metric antisymmetry",
                "Each elementary generator is skew with respect to the diagonal form with positive entries in positions zero and five."),
            Entry("universal-bracket", "so24_commutator_universal", "Elementary generator bracket",
                "The commutator of two elementary generators is the four-term contraction with the signed metric, with signs plus, minus, minus, plus in the displayed index order."),
            Entry("conformal-brackets", "conformal_algebra_commutators", "Conformal generator brackets",
                "Translations commute with one another, as do special conformal generators. Dilatation commutes with Lorentz generators and has weights plus one on translations and minus one on special conformal generators. The special conformal and translation bracket is twice the Lorentz generator minus twice the metric component times dilatation. Lorentz generators act on both vector families by the signed vector action."),
            Entry("independent-generators", "so24_basis15_linearIndependent", "Linear independence",
                "The fifteen generators with increasing index pairs are linearly independent over the reals."),
            Entry("basis-expansion", "so24_expansion", "Recovery from upper-triangular entries",
                "A metric-skew matrix is the sum of the elementary generators weighted by its upper-triangular entries times the sign of the column."),
            Entry("dimension", "so24_subspace_finrank_15", "Dimension of the orthogonal algebra",
                "The real subspace of matrices skew with respect to the six-dimensional form has dimension fifteen."),
            Entry("inversion-involution", "conformalInv_involutive", "Inversion and squared norm",
                "At a non-null point inversion takes the squared norm to its reciprocal. Applying inversion again recovers the point."),
            Entry("inversion-separation", "conformalInv_diff_normSq", "Inversion rescales squared separations",
                "For two non-null points, the separation after inversion is the original squared separation divided by the product of their squared norms."),
            Entry("inversion-derivative", "conformalInv_hasFDerivAt", "Fréchet derivative of inversion",
                "At a non-null point the derivative is inverse squared-norm scaling plus the rank-one correction from differentiating that scalar factor."),
            Entry("inversion-metric", "conformalInv_metric_pullback", "Minkowski metric pullback",
                "The derivative of inversion rescales the bilinear form by the inverse square of the point squared norm."),
            Entry("special-conformal-formula", "sct_explicit_formula", "Special conformal coordinate formula",
                "At a non-null point with nonzero special conformal denominator, translating between two inversions gives the rational special conformal map."),
            Entry("special-conformal-separation", "sct_diff_normSq", "Special conformal separation factor",
                "The transformed squared separation is divided by the product of the special conformal denominators. Nonzero denominators suffice, including for null input points."),
            Entry("cross-ratios", "crossRatios_conformal_invariant", "Invariance of both four-point ratios",
                "With non-null denominator separations, both ratios are invariant under translation, every metric-preserving Lorentz matrix, nonzero dilation, inversion of non-null points, and special conformal maps with nonzero denominators."),
            Entry("twistor-generators", "twistorRep_conformal_generators", "Chiral matrices for the conformal generators",
                "Lorentz generators map to a quarter of the gamma-matrix commutator and dilatation maps to half the chirality matrix. The translation and special conformal generators map to the gamma matrices times the left and right chiral projectors with coefficients plus and minus the imaginary unit, respectively."),
            Entry("twistor-image", "twistorRep_mem_su22", "Preservation of the Hermitian form",
                "Every image of the orthogonal subspace is traceless and skew with respect to the Hermitian form represented by the time-like Dirac matrix."),
            Entry("twistor-bracket", "twistorRep_lie_hom", "Preservation of commutators",
                "The representation carries the commutator of two matrices in the orthogonal subspace to the commutator of their four-dimensional complex images."),
            Entry("twistor-bijection", "twistorRep_bijective_su22", "Twistor Lie equivalence",
                "The real linear representation maps the metric-skew orthogonal subspace bijectively onto the traceless subspace skew for the twistor metric. Together with bracket preservation, this identifies the two Lie algebras."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
