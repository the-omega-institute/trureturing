using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRFockFactorDisjointnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent Weyl coefficients characterize the commutant on arbitrary mode index sets. Gaussian averaging detects finite-mode vacuum occupation and gives the exact criterion for a diagonal squeezed characteristic function to lie in the countable Fock folium.",
        H("Fock Weyl irreducibility and squeezed-state disjointness"),
        Blocks(
            Entry("weyl-map", "weylMap",
                "Bounded Weyl displacement",
                "View the Weyl isometry as a bounded complex-linear operator.", DescribeRole.Definition),
            Entry("commutant", "fockWeyl_commutant_scalar",
                "Scalar Fock Weyl commutant",
                "Weyl translation of the coherent kernel forces its vacuum column to be both holomorphic and antiholomorphic along each complex line. Density of coherent vectors then determines the commuting operator."),
            Entry("bicommutant", "fockWeyl_bicommutant_top",
                "Full Fock Weyl bicommutant",
                "Every bounded operator commutes with scalars, giving the full bounded operator algebra."),
            Entry("factor", "fockWeyl_isFactor",
                "Trivial Fock Weyl center",
                "An element of the center commutes with the Weyl displacements and hence acts by a scalar."),
            Entry("squeezed-char", "squeezedChar",
                "Squeezed characteristic function",
                "The diagonal covariance multiplies the squared real and imaginary quadratures by opposite exponential weights. For arbitrary parameters the characteristic function is used on finitely supported displacements.", DescribeRole.Definition),
            Entry("squeeze-coefficient", "squeezedChar_infiniteSqueeze",
                "Weyl coefficient of the infinite squeeze",
                "The unit vector constructed from square-summable squeeze parameters realizes the characteristic function."),
            Entry("squeeze-vector", "squeezed_in_fock_folium_of_summable_sq",
                "Squeezed unit vector",
                "The norm limit of finite product squeezes gives a single unit vector with the specified coefficients."),
            Entry("vacuum-proj", "vacuumProj",
                "Finite-mode vacuum projection",
                "The orthogonal coordinate projection keeps exactly the occupations that vanish on the selected modes.", DescribeRole.Definition),
            Entry("gaussian-proj", "fockWeyl_gaussian_avg_eq_vacuumProj",
                "Gaussian Weyl average",
                "Integrate coherent matrix coefficients over finite complex coordinates with planar Lebesgue measure. The mixed Gaussian integrals erase the selected coherent coordinates. Boundedness and coherent totality identify the average with the projection."),
            Entry("gaussian-squeezed", "squeezedChar_gaussian_avg",
                "Anisotropic Gaussian average",
                "The two quadrature integrals in each mode give a reciprocal hyperbolic cosine. Finite product integration gives the product of those values."),
            Entry("folium", "SqueezedInFockFolium",
                "Countable Fock folium",
                "A countable family of Fock vectors has unit total squared norm and reproduces the characteristic function on every finite set of modes.", DescribeRole.Definition),
            Entry("folium-criterion", "squeezed_in_fock_folium_iff",
                "Exact square-summability criterion",
                "Finite occupation sets capture more than half the total mass. Gaussian averages on modes disjoint from that set therefore bound the reciprocal hyperbolic-cosine products from below. The lower quadratic bound on the hyperbolic cosine gives summability."),
            Entry("excitable-criterion", "squeezed_excitable_iff_summable_sq",
                "Excitability criterion",
                "Countable Fock excitability holds exactly when the squared squeezing parameters are summable."),
            Entry("nonexcitable", "squeezed_not_excitable_of_not_summable_sq",
                "Non-excitability",
                "A nonsummable square family precludes a Fock folium representation."),
            Entry("disjoint", "squeezed_gns_disjoint_of_not_summable_sq",
                "Strict disjointness of the pure squeezed state",
                "Purity gives a scalar commutant for any cyclic realization of the state. Schur’s lemma would turn a nonzero bounded intertwiner into a unitary equivalence. The resulting Fock vector would reproduce the squeezed characteristic function on all finite-mode displacements, contradicting the summability obstruction."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
