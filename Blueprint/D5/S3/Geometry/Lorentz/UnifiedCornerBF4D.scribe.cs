using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class UnifiedCornerBF4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.";
    private static LibraryNoteRef DonnellyFreidel => LibraryNoteRef.Create("D5/L/LieTheory/donnellyfreidel2016edge");
    private static LibraryNoteRef Urbantke => LibraryNoteRef.Create("D5/L/LieTheory/urbantke1984plebanski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corner currents, area and rapidity, and the signed auxiliary-field BF reduction.",
        H("Unified corner symmetry and chiral BF reduction"),
        Blocks(
            Paragraph(Text("The normal and Yang–Mills currents share a tangential derivation action. The normal moment map admits an explicit canonical area–rapidity extension. A metric determines the signed Hodge operator on the auxiliary two-form sector, whose exact stationary elimination yields the curvature quadratic density.")),
            Describe.Lean(DescribeId.Create("corner-internal"), DeclarationHandle.Create(Prefix + "CornerInternal"),
                H("Internal Lie algebra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The internal Lie algebra is the direct product of the trace-zero two-by-two matrices and the Yang–Mills Lie algebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corner-current"), DeclarationHandle.Create(Prefix + "CornerCurrent"),
                H("Current Lie algebra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scalar extension gives the tensor product with the commutative coefficient algebra, with bracket [a⊗u,b⊗v]=ab⊗[u,v]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("current-derivation"), DeclarationHandle.Create(Prefix + "currentDerivation"),
                H("Differentiating currents"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivation acts on the coefficient factor and leaves the internal factor fixed. The product rule proves the Lie derivation law on pure tensors, and additivity extends it to all currents."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corner-derivation-hom"), DeclarationHandle.Create(Prefix + "cornerDerivationHom"),
                H("Tangential Lie action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On pure tensors the commutator of two induced derivations acts by the commutator on the coefficient. Tensor induction extends the linear and Lie homomorphism laws."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corner-algebra"), DeclarationHandle.Create(Prefix + "CornerAlgebra"),
                H("Semidirect corner Lie algebra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DonnellyFreidel),
                Blocks(Paragraph(Text("The tensor product of the coefficient and internal Lie algebras is acted upon by the selected Lie subalgebra of coefficient derivations. The resulting semidirect sum has its current component first."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("p"), DeclarationHandle.Create(Prefix + "P"),
                H("Tangential charges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The acting Lie algebra is included in the semidirect sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("j"), DeclarationHandle.Create(Prefix + "J"),
                H("Pure current charges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient and the internal generator define a pure tensor and its inclusion into the semidirect sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("g"), DeclarationHandle.Create(Prefix + "G"),
                H("Gravitational currents"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scalar extension of the first product inclusion defines a Lie homomorphism on all normal frame currents."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("y"), DeclarationHandle.Create(Prefix + "Y"),
                H("Yang–Mills currents"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scalar extension of the second product inclusion defines a Lie homomorphism on all Yang–Mills currents."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corner-bracket"), DeclarationHandle.Create(Prefix + "corner_bracket"),
                H("Corner bracket table"), StatementSource.FromAuthor(Disp(CornerBracket())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bracket of tangential generators is their commutator. A tangential generator acts on a current by differentiation of its coefficient. Two pure currents bracket by multiplying coefficients and taking the internal bracket."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corner-internal-brackets"), DeclarationHandle.Create(Prefix + "corner_internal_brackets"),
                H("Normal and gauge charge brackets"), StatementSource.FromAuthor(Disp(CornerInternalBrackets())), AssessedProvenance.FromRepo(DonnellyFreidel),
                Blocks(Paragraph(Text("Tangential derivations differentiate each coefficient factor. Within each internal summand the charge maps preserve the full tensor Lie bracket. The mixed bracket vanishes because the two internal factors commute."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corner-jacobi"), DeclarationHandle.Create(Prefix + "corner_jacobi"),
                H("Corner Jacobi identity"), StatementSource.FromAuthor(Disp(CornerJacobi())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivation action and its commutator law give a semidirect Lie algebra. The cyclic Jacobi sum vanishes by the Lie derivation identity and skew symmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantum-charge"), DeclarationHandle.Create(Prefix + "quantumCharge"),
                H("Associative charge map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal enveloping algebra gives the Lie homomorphism from corner generators into its associative commutator algebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("enveloping-commutators"), DeclarationHandle.Create(Prefix + "enveloping_commutators"),
                H("Enveloping commutator algebra"), StatementSource.FromAuthor(Disp(EnvelopingCommutators())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Lie homomorphism sends the normal and Yang–Mills brackets to the corresponding associative commutators, including vanishing mixed commutators."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("witt"), DeclarationHandle.Create(Prefix + "witt"),
                H("Laurent derivations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a Laurent monomial r zⁿ the mode indexed by m acts as −nr zᵐ⁺ⁿ. Finitely supported linear extension and the additive exponent law give the product rule."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("witt-monomial"), DeclarationHandle.Create(Prefix + "witt_monomial"),
                H("Laurent action on monomials"), StatementSource.FromAuthor(Disp(WittMonomial())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Application of the coefficient derivation to the Laurent monomial gives the shifted exponent and the factor −n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("witt-bracket"), DeclarationHandle.Create(Prefix + "witt_bracket"),
                H("Witt bracket"), StatementSource.FromAuthor(Disp(WittBracket())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating the commutator on every Laurent monomial yields the factor m−n multiplying the mode at m+n. Additive induction proves the equality on all Laurent polynomials."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laurent-current-modes"), DeclarationHandle.Create(Prefix + "laurent_current_modes"),
                H("Laurent corner current modes"), StatementSource.FromAuthor(Disp(LaurentCurrentModes())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative of zⁿ under a Witt generator is −nzᵐ⁺ⁿ. The tangential-current bracket is thus the shifted current multiplied by −n, while the current-current bracket adds exponents and takes the internal commutator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jet"), DeclarationHandle.Create(Prefix + "Jet"),
                H("Finite jet coefficient algebra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial ring is quotiented by the principal ideal generated by zᴺ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jet-witt"), DeclarationHandle.Create(Prefix + "jetWitt"),
                H("Jet derivations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonnegative Witt derivations on polynomials preserve the ideal generated by zᴺ, so they descend through the quotient map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jet-monomial"), DeclarationHandle.Create(Prefix + "jetMonomial"),
                H("Jet monomials"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The residue class of the nth power of the polynomial variable is the nth jet monomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jet-rules"), DeclarationHandle.Create(Prefix + "jet_rules"),
                H("Truncated multiplication and differentiation"), StatementSource.FromAuthor(Disp(JetRules())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quotient multiplication adds exponents, and each monomial with exponent at least N vanishes. The descended derivation acts by −n times the monomial of degree m+n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gravitational-casimir"), DeclarationHandle.Create(Prefix + "gravitationalCasimir"),
                H("Normal quadratic invariant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normal quadratic invariant is one half of the trace of the square of a trace-zero matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normal-area-casimir"), DeclarationHandle.Create(Prefix + "normal_area_casimir"),
                H("Area Casimir polynomial"), StatementSource.FromAuthor(Disp(NormalAreaCasimir())), AssessedProvenance.FromRepo(DonnellyFreidel),
                Blocks(Paragraph(Text("Trace zero determines the second diagonal entry to be minus the first. Expanding the trace of the square and determinant then gives a²+bc and minus the determinant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-area-adjoint-invariant"), DeclarationHandle.Create(Prefix + "normal_area_adjoint_invariant"),
                H("Infinitesimal adjoint invariance"), StatementSource.FromAuthor(Disp(NormalAreaAdjointInvariant())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cyclic invariance of matrix trace cancels the linear variation of the quadratic invariant along a commutator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-area-variation"), DeclarationHandle.Create(Prefix + "normal_area_variation"),
                H("Exact quadratic adjoint variation"), StatementSource.FromAuthor(Disp(NormalAreaVariation())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expansion of the quadratic invariant along the affine line through the commutator direction has its linear term zero by cyclic trace."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ym-casimir"), DeclarationHandle.Create(Prefix + "ymCasimir"),
                H("Yang–Mills quadratic invariant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic function on an internal momentum is its pairing with itself under the chosen invariant bilinear form."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("internal-casimir-invariant"), DeclarationHandle.Create(Prefix + "internal_casimir_invariant"),
                H("Yang–Mills infinitesimal invariance"), StatementSource.FromAuthor(Disp(InternalCasimirInvariant())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the quadratic function along the adjoint direction. Lie invariance of the pairing cancels the two linear terms, leaving the original value and the quadratic term."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corner-observable"), DeclarationHandle.Create(Prefix + "CornerObservable"),
                H("Coordinate observables"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An observable takes the four real coordinates q, p, relative rapidity and area."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corner-poisson"), DeclarationHandle.Create(Prefix + "cornerPoisson"),
                H("Darboux bracket"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bracket is the sum of the antisymmetric products of the actual coordinate derivatives in the q,p and rapidity,area pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-h"), DeclarationHandle.Create(Prefix + "chartH"),
                H("Darboux generator H"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal generator is −2p."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-e"), DeclarationHandle.Create(Prefix + "chartE"),
                H("Darboux generator E"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive generator is exp(q)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-f"), DeclarationHandle.Create(Prefix + "chartF"),
                H("Darboux generator F"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The opposite generator is (area²−p²)exp(−q)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-rapidity"), DeclarationHandle.Create(Prefix + "chartRapidity"),
                H("Relative rapidity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The third coordinate is the relative rapidity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-area"), DeclarationHandle.Create(Prefix + "chartArea"),
                H("Area coordinate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fourth coordinate is the area parameter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("area-boost-pair"), DeclarationHandle.Create(Prefix + "area_boost_pair"),
                H("Exact Darboux brackets and area"), StatementSource.FromAuthor(Disp(AreaBoostPair())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate derivatives of the generators give the three normal Lie brackets and the canonical rapidity–area bracket. The identity exp(q)exp(−q)=1 gives the quadratic Casimir equal to area squared. The rapidity bracket with F equals 2 area exp(−q)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chart-moment"), DeclarationHandle.Create(Prefix + "chartMoment"),
                H("Trace-dual moment matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moment matrix has diagonal entries H/2 and −H/2, upper entry F and lower entry E."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-moment-casimir"), DeclarationHandle.Create(Prefix + "chart_moment_casimir"),
                H("Moment-map area"), StatementSource.FromAuthor(Disp(ChartMomentCasimir())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normal area formula applied to the trace-dual moment matrix yields area squared by the Darboux realization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-hodge"), DeclarationHandle.Create(Prefix + "realHodge"),
                H("Real metric Hodge star"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The volume is the positive square root of the absolute metric determinant. The star is this volume times the wedge matrix times the exterior square of the inverse metric."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("metric-sign"), DeclarationHandle.Create(Prefix + "metricSign"),
                H("Determinant sign"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sign parameter equals minus one for a negative metric determinant and plus one for a positive determinant."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("real-hodge-structure"), DeclarationHandle.Create(Prefix + "real_hodge_structure"),
                H("Real Hodge square and wedge adjoint"), StatementSource.FromAuthor(Disp(RealHodgeStructure())), AssessedProvenance.FromRepo(Urbantke),
                Blocks(Paragraph(Text("Multiplicativity and the complementary-minor determinant identity for exterior squares give the Hodge square. Symmetry of the inverse metric and the wedge involution give wedge self-adjointness. The square is negative identity for negative determinant and positive identity for positive determinant, which includes Euclidean metrics."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("urbantke-lorentz-phase"), DeclarationHandle.Create(Prefix + "urbantke_lorentz_phase"),
                H("Chiral phase conversion"), StatementSource.FromAuthor(Disp(UrbantkeLorentzPhase())), AssessedProvenance.FromRepo(Urbantke),
                Blocks(Paragraph(Text("For a nondegenerate complex triple wedge-orthogonal to its conjugate, the Urbantke reconstruction supplies a real representative with negative determinant. If its complex scale is l and the oriented positive real volume is v, the chiral phase is l²v divided by the Urbantke density. Its square is −1 by the determinant identity, so the phase is either i or −i. Exterior scaling gives the real Hodge map times the inverse phase as the complex chiral star, and the triple is the corresponding eigenspace."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("urbantke-real-hodge"), DeclarationHandle.Create(Prefix + "urbantke_real_hodge"),
                H("Real triple and positive Hodge square"), StatementSource.FromAuthor(Disp(UrbantkeRealHodge())), AssessedProvenance.FromRepo(Urbantke),
                Blocks(Paragraph(Text("The determinant of the cubic reconstruction is the square of the wedge Gram determinant divided by 64. A real nondegenerate triple therefore has a positive determinant and a Hodge operator squaring to the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("null-screen-hodge"), DeclarationHandle.Create(Prefix + "null_screen_hodge"),
                H("Lorentzian null screen"), StatementSource.FromAuthor(Disp(NullScreenHodge())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the diagonal metric with entries −1,1,1,1, the real Hodge operator squares to minus identity. The screen vectors are orthogonal to the null generator and have Euclidean Gram matrix in this metric."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bf-density"), DeclarationHandle.Create(Prefix + "bfDensity"),
                H("Block-split BF density"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the gravitational term fixed, the Yang–Mills term is the wedge pairing of the auxiliary field with curvature minus half the squared coupling times the pairing with its Hodge transform."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bf-stationary"), DeclarationHandle.Create(Prefix + "bfStationary"),
                H("Auxiliary-field stationarity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Stationarity requires the first variation coefficient to vanish against every variation of the auxiliary field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bf-variation"), DeclarationHandle.Create(Prefix + "bf_variation"),
                H("Exact BF variation"), StatementSource.FromAuthor(Disp(BfVariation())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bilinearity, symmetry and wedge self-adjointness give the full quadratic variation in the scalar parameter. The coefficient of the linear term is the pairing with F−g²JB."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bf-critical"), DeclarationHandle.Create(Prefix + "bfCritical"),
                H("Critical field"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The candidate stationary field is the signed Hodge transform of the curvature divided by the squared coupling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bf-stationary-iff"), DeclarationHandle.Create(Prefix + "bf_stationary_iff"),
                H("Unique stationary auxiliary field"), StatementSource.FromAuthor(Disp(BfStationaryIff())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nondegeneracy reduces all vanishing first coefficients to g²JB=F. The star squares to the sign times identity, so when the coupling is nonzero this equation has the stated unique solution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bf-complete-square"), DeclarationHandle.Create(Prefix + "bf_complete_square"),
                H("BF completion of the square"), StatementSource.FromAuthor(Disp(BfCompleteSquare())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translate the auxiliary field by the stationary field. The exact variation has no linear term, and its constant term uses g²JB*=F. Symmetry converts the stationary BF pairing into the signed curvature pairing divided by the squared coupling."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bf-zero-coupling"), DeclarationHandle.Create(Prefix + "bf_zero_coupling"),
                H("Zero coupling degeneracy"), StatementSource.FromAuthor(Disp(BfZeroCoupling())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At zero coupling the first variation is independent of the auxiliary field. Nondegeneracy then makes it vanish precisely when the curvature is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("color-wedge"), DeclarationHandle.Create(Prefix + "colorWedge"),
                H("Yang–Mills wedge metric"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The wedge matrix is tensored with the symmetric color pairing using the Kronecker product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("color-hodge"), DeclarationHandle.Create(Prefix + "colorHodge"),
                H("Hodge on colored forms"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real Hodge matrix acts on form indices while the identity acts on color indices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("urbantke-bf-yang-mills"), DeclarationHandle.Create(Prefix + "urbantke_bf_yang_mills"),
                H("Metric BF reduction"), StatementSource.FromAuthor(Disp(UrbantkeBfYangMills())), AssessedProvenance.FromRepo(Urbantke),
                Blocks(Paragraph(Text("The determinant of the wedge matrix is nonzero because it squares to identity. Kronecker multiplication transports symmetry, nondegeneracy, wedge adjointness and the Hodge square to the color space. The abstract BF stationarity and completion identities therefore apply for every symmetric invertible real metric and symmetric invertible color pairing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("urbantke-bf-on-shell"), DeclarationHandle.Create(Prefix + "urbantke_bf_on_shell"),
                H("Signed on-shell density"), StatementSource.FromAuthor(Disp(UrbantkeBfOnShell())), AssessedProvenance.FromRepo(Urbantke),
                Blocks(Paragraph(Text("Substituting the stationary field makes the translated quadratic term vanish. A negative determinant gives coefficient −1/(2g²), and a positive determinant gives coefficient +1/(2g²)."))), DescribeRole.Theorem)),
        []));

    private static Formula CornerBracket()
    {
        Formula x = V("X"), z = V("Z"), a = V("a"), b = V("b"), u = V("u"), v = V("v");
        return CornerContext(All(And(
            Equal(Bracket(Call("P", x), Call("P", z)), Call("P", Bracket(x, z))),
            Equal(Bracket(Call("P", x), Call("J", a, u)), Call("J", Apply(x, a), u)),
            Equal(Bracket(Call("J", a, u), Call("J", b, v)), Call("J", Multiply(a, b), Bracket(u, v)))),
            ("X", V("L")), ("Z", V("L")), ("a", V("A")), ("b", V("A")),
            ("u", Internal), ("v", Internal)));
    }

    private static Formula CornerInternalBrackets()
    {
        Formula x = V("X"), u = V("u"), v = V("v"), l = V("l"), eta = V("eta");
        Formula d = Tensor(x, Identity);
        return CornerContext(All(And(
            Equal(Bracket(Call("P", x), Call("G", u)), Call("G", Apply(d, u))),
            Equal(Bracket(Call("P", x), Call("Y", l)), Call("Y", Apply(d, l))),
            Equal(Bracket(Call("G", u), Call("G", v)), Call("G", Bracket(u, v))),
            Equal(Bracket(Call("Y", l), Call("Y", eta)), Call("Y", Bracket(l, eta))),
            Equal(Bracket(Call("G", u), Call("Y", l)), Zero)),
            ("X", V("L")), ("u", GravityCurrent), ("v", GravityCurrent),
            ("l", GaugeCurrent), ("eta", GaugeCurrent)));
    }

    private static Formula CornerJacobi()
    {
        Formula x = V("x"), y = V("y"), z = V("z");
        Formula corner = Call("CornerAlgebra", V("A"), V("L"), V("gYM"));
        return CornerContext(All(Equal(
            Add(Add(Bracket(x, Bracket(y, z)), Bracket(y, Bracket(z, x))), Bracket(z, Bracket(x, y))), Zero),
            ("x", corner), ("y", corner), ("z", corner)));
    }

    private static Formula EnvelopingCommutators()
    {
        Formula u = V("u"), v = V("v"), l = V("l"), eta = V("eta");
        Formula QG(Formula a) => Call("Q", Call("G", a));
        Formula QY(Formula a) => Call("Q", Call("Y", a));
        return CornerContext(All(And(
            Equal(Bracket(QG(u), QG(v)), QG(Bracket(u, v))),
            Equal(Bracket(QY(l), QY(eta)), QY(Bracket(l, eta))),
            Equal(Bracket(QG(u), QY(l)), Zero)),
            ("u", GravityCurrent), ("v", GravityCurrent), ("l", GaugeCurrent), ("eta", GaugeCurrent)));
    }

    private static Formula WittMonomial()
    {
        Formula m = V("m"), n = V("n"), r = V("r");
        return All(Equal(Apply(Witt(m), Multiply(r, Power(V("z"), n))),
            Scale(Multiply(Negative(n), r), Power(V("z"), Add(m, n)))),
            ("m", Integers), ("n", Integers), ("r", Reals));
    }

    private static Formula WittBracket()
    {
        Formula m = V("m"), n = V("n");
        return All(Equal(Bracket(Witt(m), Witt(n)), Scale(Subtract(m, n), Witt(Add(m, n)))),
            ("m", Integers), ("n", Integers));
    }

    private static Formula LaurentCurrentModes()
    {
        Formula m = V("m"), n = V("n"), u = V("u"), v = V("v");
        Formula Mode(Formula k, Formula t) => Call("J", Power(V("z"), k), t);
        return All(And(
            Equal(Bracket(Call("P", Witt(m)), Mode(n, u)), Scale(Negative(n), Mode(Add(m, n), u))),
            Equal(Bracket(Mode(m, u), Mode(n, v)), Mode(Add(m, n), Bracket(u, v)))),
            ("gYM", Call("LieAlgebra", Reals)), ("m", Integers), ("n", Integers),
            ("u", Internal), ("v", Internal));
    }

    private static Formula JetRules()
    {
        Formula m = V("m"), n = V("n"), N = V("N");
        Formula Monomial(Formula k) => Call("jetMonomial", N, k);
        return All(And(
            Equal(Apply(Call("jetWitt", m, N), Monomial(n)), Scale(Negative(n), Monomial(Add(m, n)))),
            Equal(Multiply(Monomial(m), Monomial(n)), Monomial(Add(m, n))),
            When(new Formula.Relation(N, FormulaRelationOperator.LessThanOrEqual, n), Equal(Monomial(n), Zero))),
            ("m", Naturals), ("n", Naturals), ("N", Naturals));
    }

    private static Formula NormalAreaCasimir()
    {
        Formula m = V("M"), c = Call("CG", m);
        Formula Entry(int i, int j) => Apply(m, Num(i), Num(j));
        return All(And(Equal(c, Negative(Det(m))),
            Equal(c, Add(Square(Entry(0, 0)), Multiply(Entry(0, 1), Entry(1, 0))))),
            ("M", Sl2));
    }

    private static Formula NormalAreaAdjointInvariant()
    {
        Formula u = V("U"), m = V("M"), b = Bracket(u, m);
        return All(Equal(Divide(Call("tr", Add(Multiply(b, m), Multiply(m, b))), Num(2)), Zero),
            ("U", Sl2), ("M", Sl2));
    }

    private static Formula NormalAreaVariation()
    {
        Formula u = V("U"), m = V("M"), t = V("t"), b = Bracket(u, m);
        return All(Equal(Call("CG", Add(m, Scale(t, b))),
            Add(Call("CG", m), Multiply(Square(t), Call("CG", b)))),
            ("U", Sl2), ("M", Sl2), ("t", Reals));
    }

    private static Formula InternalCasimirInvariant()
    {
        Formula k = V("kappa"), u = V("u"), v = V("nu"), t = V("t"), y = V("Y");
        Formula x = V("x"), a = V("a"), b = V("b");
        Formula invariant = All(Equal(Apply(k, Bracket(x, a), b), Negative(Apply(k, a, Bracket(x, b)))),
            ("x", y), ("a", y), ("b", y));
        return All(When(invariant, Equal(Call("CY", k, Add(v, Scale(t, Bracket(u, v)))),
            Add(Call("CY", k, v), Multiply(Square(t), Call("CY", k, Bracket(u, v)))))),
            ("Y", Call("LieAlgebra", Reals)), ("kappa", Call("Bilin", Reals, y)),
            ("u", y), ("nu", y), ("t", Reals));
    }

    private static Formula AreaBoostPair()
    {
        Formula h = V("H"), e = V("E"), f = V("F"), gamma = V("Gamma"), a = V("A");
        Formula Poisson(Formula x, Formula y) => Seq(OpenBrace, x, Comma, Sp, y, CloseBrace);
        return ChartContext(And(
            Equal(Poisson(h, e), Multiply(Num(2), e)),
            Equal(Poisson(h, f), Multiply(Negative(Num(2)), f)),
            Equal(Poisson(e, f), h),
            Equal(Divide(Add(Square(h), Multiply(Multiply(Num(4), e), f)), Num(4)), Square(a)),
            Equal(Poisson(gamma, a), One),
            Equal(Poisson(gamma, f), Multiply(Multiply(Num(2), a), Call("exp", Negative(V("q")))))));
    }

    private static Formula ChartMomentCasimir() =>
        ChartContext(Equal(Call("CG", Call("chartMoment", V("q"), V("p"), V("Gamma"), V("A"))), Square(V("A"))));

    private static Formula RealHodgeStructure()
    {
        Formula g = V("g"), j = Call("realHodge", g), s = Call("metricSign", g), w = Call("W", Reals);
        return All(When(And(Equal(Transpose(g), g), Nonzero(Det(g))), And(
            Equal(j, Call("hodge", g, Seq(Sqrt, Grp(new Formula.Absolute(Det(g)))))),
            Or(Equal(s, Negative(One)), Equal(s, One)),
            Equal(Square(j), Scale(s, Identity)),
            Equal(Multiply(Transpose(j), w), Multiply(w, j)))),
            ("g", Metric(Reals)));
    }

    private static Formula UrbantkeLorentzPhase()
    {
        Formula b = V("B"), g = V("g"), l = V("l"), phase = V("phase"), w = Call("W", Complexes);
        Formula u = Call("U", b), d = Call("density", b), i = V("i");
        Formula j = Call("complexify", Call("realHodge", g));
        return All(When(And(Nonzero(Det(Call("Q", b))),
            Equal(Multiply(Multiply(Transpose(b), w), Seq(Overline, Grp(b))), Zero)),
            Exist(And(Nonzero(l), Equal(Transpose(g), g), Less(Det(g), Zero),
                Equal(u, Scale(l, Call("complexify", g))), Or(Equal(phase, i), Equal(phase, Negative(i))),
                Equal(Call("hodge", u, d), Scale(Power(phase, Negative(One)), j)),
                Equal(Multiply(j, b), Scale(phase, b))),
                ("g", Metric(Reals)), ("l", Complexes), ("phase", Complexes))),
            ("B", Triple(Complexes)));
    }

    private static Formula UrbantkeRealHodge()
    {
        Formula b = V("B"), u = Call("U", b);
        return All(When(Nonzero(Det(Call("Q", b))),
            And(Less(Zero, Det(u)), Equal(Square(Call("realHodge", u)), Identity))),
            ("B", Triple(Reals)));
    }

    private static Formula NullScreenHodge()
    {
        Formula r = V("r"), a = V("a"), b = V("b");
        Formula g = Call("diag", Negative(One), One, One, One);
        Formula Frame(Formula k) => Call("screenFrame", r, k);
        Formula Pair(Formula x, Formula y) => Multiply(Multiply(Transpose(x), g), y);
        Formula fin2 = Call("Fin", Num(2));
        return All(And(Equal(Square(Call("realHodge", g)), Negative(Identity)),
            All(Equal(Pair(Frame(a), Call("nullGenerator", r)), Zero), ("a", fin2)),
            All(And(When(Equal(a, b), Equal(Pair(Frame(a), Frame(b)), One)),
                When(NotEqual(a, b), Equal(Pair(Frame(a), Frame(b)), Zero))), ("a", fin2), ("b", fin2))),
            ("r", Call("FutureNullRay", Complexes)));
    }

    private static Formula BfVariation()
    {
        Formula w = V("W"), j = V("J"), g = V("g"), grav = V("LG"), t = V("t"), f = V("F"), b = V("B"), v = V("v");
        Formula result = Equal(Density(w, j, grav, g, f, Add(b, Scale(t, v))),
            Subtract(Add(Density(w, j, grav, g, f, b),
                Multiply(t, Apply(w, v, Subtract(f, Scale(Square(g), Apply(j, b)))))),
                Multiply(Multiply(Divide(Square(g), Num(2)), Square(t)), Apply(w, v, Apply(j, v)))));
        return BfContext(All(When(And(Symmetric(w), Adjoint(w, j)), result),
            ("LG", Reals), ("g", Reals), ("t", Reals), ("F", V("V")), ("B", V("V")), ("v", V("V"))));
    }

    private static Formula BfStationaryIff()
    {
        Formula w = V("W"), j = V("J"), s = V("s"), g = V("g"), f = V("F"), b = V("B");
        return BfContext(All(When(And(Nondegenerate(w), HodgeConditions(j, s, g)),
            StationaryResult(w, j, s, g, f, b)),
            ("s", Reals), ("g", Reals), ("F", V("V")), ("B", V("V"))));
    }

    private static Formula BfCompleteSquare()
    {
        Formula w = V("W"), j = V("J"), s = V("s"), g = V("g"), grav = V("LG"), f = V("F"), b = V("B");
        return BfContext(All(When(And(Symmetric(w), Adjoint(w, j), HodgeConditions(j, s, g)),
            SquareResult(w, j, s, g, grav, f, b)),
            ("s", Reals), ("g", Reals), ("LG", Reals), ("F", V("V")), ("B", V("V"))));
    }

    private static Formula BfZeroCoupling()
    {
        Formula w = V("W"), j = V("J"), f = V("F"), b = V("B");
        return BfContext(All(When(Nondegenerate(w),
            Equivalent(Call("bfStationary", w, j, Zero, f, b), Equal(f, Zero))),
            ("F", V("V")), ("B", V("V"))));
    }

    private static Formula UrbantkeBfYangMills()
    {
        Formula m = V("metric"), k = V("kappa"), g = V("g"), grav = V("LG"), f = V("F"), b = V("B");
        Formula w = Call("colorWedge", k), j = Call("colorHodge", m), s = Call("metricSign", m);
        return ColorContext(All(When(ColorConditions(m, k, g), And(
            StationaryResult(w, j, s, g, f, b), SquareResult(w, j, s, g, grav, f, b))),
            ("g", Reals), ("LG", Reals), ("F", ColorVector), ("B", ColorVector)));
    }

    private static Formula UrbantkeBfOnShell()
    {
        Formula m = V("metric"), k = V("kappa"), g = V("g"), grav = V("LG"), f = V("F");
        Formula w = Call("colorWedge", k), j = Call("colorHodge", m), s = Call("metricSign", m);
        Formula density = Density(w, j, grav, g, f, Critical(j, s, g, f));
        Formula curvature = Multiply(Divide(One, Multiply(Num(2), Square(g))), Apply(w, f, Apply(j, f)));
        return ColorContext(All(When(ColorConditions(m, k, g), And(
            When(Less(Det(m), Zero), Equal(density, Subtract(grav, curvature))),
            When(new Formula.Relation(Zero, FormulaRelationOperator.LessThanOrEqual, Det(m)),
                Equal(density, Add(grav, curvature))))),
            ("g", Reals), ("LG", Reals), ("F", ColorVector)));
    }

    private static Formula Density(Formula w, Formula j, Formula grav, Formula g, Formula f, Formula b) =>
        Call("bfDensity", w, j, grav, g, f, b);
    private static Formula Critical(Formula j, Formula s, Formula g, Formula f) => Call("bfCritical", j, s, g, f);
    private static Formula StationaryResult(Formula w, Formula j, Formula s, Formula g, Formula f, Formula b) =>
        Equivalent(Call("bfStationary", w, j, g, f, b), Equal(b, Critical(j, s, g, f)));

    private static Formula SquareResult(Formula w, Formula j, Formula s, Formula g, Formula grav, Formula f, Formula b)
    {
        Formula difference = Subtract(b, Critical(j, s, g, f));
        return Equal(Density(w, j, grav, g, f, b),
            Subtract(Add(grav, Multiply(Divide(s, Multiply(Num(2), Square(g))), Apply(w, f, Apply(j, f)))),
                Multiply(Divide(Square(g), Num(2)), Apply(w, difference, Apply(j, difference)))));
    }

    private static Formula Symmetric(Formula w) =>
        All(Equal(Apply(w, V("x"), V("y")), Apply(w, V("y"), V("x"))), ("x", V("V")), ("y", V("V")));
    private static Formula Adjoint(Formula w, Formula j) =>
        All(Equal(Apply(w, Apply(j, V("x")), V("y")), Apply(w, V("x"), Apply(j, V("y")))), ("x", V("V")), ("y", V("V")));
    private static Formula Nondegenerate(Formula w) =>
        All(When(All(Equal(Apply(w, V("v"), V("x")), Zero), ("v", V("V"))), Equal(V("x"), Zero)), ("x", V("V")));
    private static Formula HodgeConditions(Formula j, Formula s, Formula g) => And(
        Equal(Square(s), One), All(Equal(Apply(j, Apply(j, V("x"))), Scale(s, V("x"))), ("x", V("V"))), Nonzero(g));
    private static Formula ColorConditions(Formula m, Formula k, Formula g) =>
        And(Equal(Transpose(m), m), Nonzero(Det(m)), Equal(Transpose(k), k), Nonzero(Det(k)), Nonzero(g));

    private static Formula CornerContext(Formula body) => All(body,
        ("A", Call("CommAlgebra", Reals)), ("gYM", Call("LieAlgebra", Reals)),
        ("L", Call("LieSubalgebra", Call("Der", Reals, V("A")))));
    private static Formula ChartContext(Formula body) => All(body,
        ("q", Reals), ("p", Reals), ("Gamma", Reals), ("A", Reals));
    private static Formula BfContext(Formula body) => All(body,
        ("V", Call("VectorSpace", Reals)), ("W", Call("Bilin", Reals, V("V"))), ("J", Call("End", Reals, V("V"))));
    private static Formula ColorContext(Formula body) => All(body,
        ("iota", V("FiniteIndexType")), ("metric", Metric(Reals)),
        ("kappa", Call("Mat", V("iota"), V("iota"), Reals)));

    private static Formula ColorVector => Power(Reals, Seq(Num(6), Sp, Times, Sp, Apply(V("card"), V("iota"))));
    private static Formula Internal => Seq(Sl2, Sp, Times, Sp, V("gYM"));
    private static Formula GravityCurrent => Tensor(V("A"), Sl2);
    private static Formula GaugeCurrent => Tensor(V("A"), V("gYM"));
    private static Formula Sl2 => Call("sl", Num(2), Reals);
    private static Formula Reals => NumberField("R");
    private static Formula Complexes => NumberField("C");
    private static Formula Integers => NumberField("Z");
    private static Formula Naturals => NumberField("N");
    private static Formula Zero => Num(0);
    private static Formula One => Num(1);
    private static Formula Identity => V("I");
    private static Formula V(string name) => F.Id(name);
    private static Formula NumberField(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Metric(Formula field) => Call("Mat", Num(4), Num(4), field);
    private static Formula Triple(Formula field) => Call("Mat", Num(6), Num(3), field);
    private static Formula Witt(Formula m) => new Formula.Subscript(V("L"), m);
    private static Formula Bracket(Formula a, Formula b) => Seq(OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula Tensor(Formula a, Formula b) => Call("Tensor", a, b);
    private static Formula Scale(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, b);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Det(Formula value) => Call("det", value);
    private static Formula Transpose(Formula value) => Power(value, V("T"));
    private static Formula Square(Formula value) => Power(value, Num(2));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negative(Formula value) => new Formula.Negate(value);
    private static Formula Nonzero(Formula value) => NotEqual(value, Zero);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula When(Formula assumption, Formula conclusion) => new Formula.Logic(assumption, FormulaLogicOperator.Implies, conclusion);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] terms) =>
        terms.Reverse().Aggregate((right, left) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables.Select(v =>
            new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Domain))], body);
    private static Formula Exist(Formula body, params (string Name, Formula Domain)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables.Select(v =>
            new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Domain))], body);
}
