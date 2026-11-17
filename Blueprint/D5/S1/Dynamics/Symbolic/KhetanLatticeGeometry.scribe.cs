using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanLatticeGeometryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual lattice-fiber cancellation forces an affine product and transports its given exact cover.",
        H("The actual lattice geometry of the two-direction six-cell branch"),
        Blocks(
            Paragraph(Text(
                "The domain is the full integer lattice. A tile F consists of six arbitrary "
                + "lattice points, its integer differences span the lattice, and T is the "
                + "given exact-cover complement. The geometric input is cancellation on every "
                + "occupied fiber in two nonparallel primitive directions, with a common nonzero "
                + "complex root for each direction. The roots need not have unit modulus. "
                + "The implication from Laurent line factors to these cancellation equations "
                + "is a separate supplier; no polynomial factorization is assumed proved here.")),
            Describe.Lean(
                DescribeId.Create("lattice"), DeclarationHandle.Create(Owner + "Lattice"),
                H("The full integer lattice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lattice is the product of two copies of the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("det"), DeclarationHandle.Create(Owner + "det"),
                H("The integral alternating determinant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "det(a,b)=a₁b₂−a₂b₁. Nonzero det(u,v) expresses independence. "
                    + "The occupied incidence keys are det(u,p) and det(p,v), evaluated only "
                    + "at actual points p of F."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("primitive"), DeclarationHandle.Create(Owner + "Primitive"),
                H("Primitive integer directions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A direction u is primitive when the integer gcd of its two coordinates "
                    + "is one. Bézout then identifies every integral point on a parallel line "
                    + "with an integer multiple of u relative to any integral base point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber-coordinate"), DeclarationHandle.Create(Owner + "fiberCoordinate"),
                H("An integral coordinate on each primitive fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate is gcdA(u₁,u₂)z₁+gcdB(u₁,u₂)z₂. Under the primitive "
                    + "and parallel hypotheses the proof derives z=fiberCoordinate(u,z)u. "
                    + "Thus the cancellation exponents are integers attached to actual differences."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber"), DeclarationHandle.Create(Owner + "fiber"),
                H("An actual occupied fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "fiber(F,u,p) filters the original F by det(u,q)=det(u,p). For primitive "
                    + "u this is precisely F intersected with p+Zu. No missing intersection "
                    + "of two lines is inserted into this set."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber-cancellation"), DeclarationHandle.Create(Owner + "FiberCancellation"),
                H("Cancellation at one common nonzero root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "FiberCancellation(F,u,λ) requires λ≠0 and, for every p in F, the sum "
                    + "of λ to the integer fiberCoordinate(u,q−p) over its actual fiber to "
                    + "vanish. This uses positive geometric offsets. A negative-mask "
                    + "convention supplies the inverse root, not a different tile or tiling."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-difference-span"), DeclarationHandle.Create(Owner + "FullDifferenceSpan"),
                H("Full integer-difference span"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Z-submodule spanned by all p−q with p,q in F is the whole lattice. "
                    + "Real linear span would not supply the lattice automorphism or gcd condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frame"), DeclarationHandle.Create(Owner + "frame"),
                H("The candidate integral frame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "frame(a,u)(i,j)=ia+ju is a Z-linear map. Its bijectivity is proved "
                    + "from the actual grid and full integer-difference span."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("affine-grid"), DeclarationHandle.Create(Owner + "AffineGrid"),
                H("The affine Minkowski grid"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AffineGrid(F,p,a,u,b,c) means exactly F=p+{0,a}+{0,bu,cu}, expressed "
                    + "as the image of {0,1}×{0,b,c}. It describes the original set F."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-cover-count"), DeclarationHandle.Create(Owner + "exactCoverCount"),
                H("The exact-cover window of the given complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "exactCoverCount(F,T,x) is the natural-number sum of the indicators of "
                    + "T(x−f) over f in F. A value of one expresses existence and uniqueness "
                    + "of the covering translate at the actual site x."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-cover"), DeclarationHandle.Create(Owner + "ExactCover"),
                H("Exact coverage of every lattice site"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ExactCover(F,T) requires the window count to be one for every integer "
                    + "lattice site. T is unrestricted apart from this exact-cover condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("period"), DeclarationHandle.Create(Owner + "Period"),
                H("A period of the original anchor predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Period(T,v) means T(x+v) if and only if T(x), for every x in the full "
                    + "lattice. Nonzero periods are supplied explicitly by the final theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("indicator"), DeclarationHandle.Create(Owner + "indicator"),
                H("The zero-one configuration of the given complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "indicator(T,x) is one at anchors and zero elsewhere. Its orbit closure "
                    + "uses the pointwise product topology on natural-number-valued configurations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-direction-cancellation-grid"),
                DeclarationHandle.Create(Owner + "two_direction_cancellation_grid"),
                H("Two cancellation directions force actual grid realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A singleton occupied fiber has cancellation sum one. Hence every "
                        + "occupied row and column has at least two points. Joint injectivity "
                        + "of the determinant keys makes the bipartite incidence simple. "
                        + "Double counting six actual points bounds each occupied key set "
                        + "between two and three.")),
                    Paragraph(Text(
                        "Write D=det(u,v)≠0 and μ=exp(log(λ)/D). Then μ≠0 and μ^D=λ. "
                        + "The character χ(q)=μ^det(q,v) is constant on each v-fiber. "
                        + "On a u-fiber based at p, q−p=ku gives χ(q)=χ(p)λ^k, "
                        + "so its character sum vanishes. Every exponent is an integer "
                        + "determinant or an integer coefficient of an actual point difference; "
                        + "this construction uses no virtual lattice intersection.")),
                    Paragraph(Text(
                        "The private incidence suppliers in this geometry module are occupied_key_bounds, "
                        + "nonzero_weight_incidence and complete_incidence_of_two. The cancellation "
                        + "supplier in turn uses missing_column_weight_eq_zero, valid for arbitrary "
                        + "finite objects, key types, complex weights and positive column degree d. "
                        + "If both occupied key sets had cardinality three, all six fiber "
                        + "degrees would be two. Summing by columns gives twice the total of "
                        + "the three nonzero column weights; summing by rows gives zero. "
                        + "Thus the total column weight is zero. Any occupied row contains "
                        + "two of the three columns and also has zero weight, forcing the "
                        + "single omitted column weight to be zero, a contradiction. "
                        + "This excludes the six-cycle by counting rather than enumeration.")),
                    Paragraph(Text(
                        "One occupied key set therefore has cardinality two, the other "
                        + "three. The injective incidence image has six elements and is a "
                        + "subset of a six-element Cartesian product, so it equals that "
                        + "product. All six intersections now have witnesses in F. Choosing "
                        + "the two actual rows and their three actual matched points, "
                        + "independence makes the transverse displacement constant. "
                        + "The result is F=p+{0,a}+{0,bw,cw}, where w is u or v, "
                        + "b and c are nonzero and distinct, and det(a,w)≠0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-span-grid-normalization"),
                DeclarationHandle.Create(Owner + "full_span_grid_normalization"),
                H("Full integer span gives unimodularity and coprimality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every difference of grid points lies in the range of frame(a,u). "
                        + "The full-span hypothesis therefore makes this range the whole "
                        + "integer lattice. Independence makes the frame injective, yielding "
                        + "the Z-linear equivalence e(i,j)=ia+ju. Preimages of (1,0) and "
                        + "(0,1) give an integer inverse determinant, so det(a,u)=±1.")),
                    Paragraph(Text(
                        "Let d=gcd(b,c). The points whose second coordinate under e inverse "
                        + "is divisible by d form a Z-submodule. Every grid difference lies "
                        + "in it; full difference span makes it the whole lattice. Applying "
                        + "this to e(0,1) gives d dividing one, hence d=1. In particular, "
                        + "gcd one and unimodularity are conclusions with full integer-span "
                        + "proofs, not extra geometric assumptions."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-direction-exact-cover-periodic"),
                DeclarationHandle.Create(Owner + "two_direction_exact_cover_periodic"),
                H("Transport the given exact cover and its product period"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coordinate complement is T₀(i,j)=T(e(i,j)−p), equivalently "
                        + "e inverse applied to T+p. The finite-sum transport identity is "
                        + "productWindowCount(T₀,b,c,x,y)=exactCoverCount(F,T,e(x,y)). "
                        + "Because e is onto, exact coverage in these coordinates is "
                        + "equivalent to exact coverage on the original lattice.")),
                    Paragraph(Text(
                        "The existing product_three_exact_cover_periodic theorem supplies "
                        + "period (2,0) or (0,3) for this very T₀. Under the affine pullback, "
                        + "Period(T₀,z) is equivalent to Period(T,e(z)), in both directions. "
                        + "Thus T has period 2a or 3w. Injectivity of e proves both candidate "
                        + "vectors nonzero. The original given complement has been followed "
                        + "throughout; no alternate periodic tiling is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-direction-orbit-closure-periodic"),
                DeclarationHandle.Create(Owner + "two_direction_orbit_closure_periodic"),
                H("One nonzero period fixes the whole given orbit closure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/FiniteGeometry/khetan2026nonconvex"),
                    LibraryNoteRef.Create("D5/L/FiniteGeometry/hervakari2023forced"),
                    LibraryNoteRef.Create("D5/L/FiniteGeometry/tanzhang2026periodictilings")),
                Blocks(
                    Paragraph(Text(
                        "Every translate of the indicator of T has the same period t. "
                        + "Translation by t is continuous on the configuration space and "
                        + "its fixed-point set is closed. The entire orbit closure of "
                        + "this given T therefore lies in that fixed-point set.")),
                    Paragraph(Text(
                        "This is the two-direction branch of the full six-cell question. "
                        + "A complete resolution also requires the line-factor-to-fiber "
                        + "cancellation supplier and the branch with at most one line-factor "
                        + "direction. Neither is asserted by these geometric statements. "
                        + "The primary question is Khetan, arXiv:2607.09830v2, Conjecture 2 "
                        + "and §3.5, with integer difference span as in Definition 1.4. "
                        + "Herva–Kari, arXiv:2301.05232v1, §3 Theorem 2, supplies the "
                        + "general finitary integral periodizer statement relevant to the "
                        + "other branch. Tan–Zhang, arXiv:2609.26576v1, Theorem 1.1, "
                        + "already proves existence of some fully periodic six-cell complement, "
                        + "without asserting that it belongs to the orbit closure of a given T. "
                        + "These comparisons do not assert a complete accepted formal resolution "
                        + "or establish literature priority."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity"))]));
}
