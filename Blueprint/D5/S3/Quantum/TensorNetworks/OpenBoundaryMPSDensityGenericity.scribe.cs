using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSDensityGenericityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An intrinsic dense real-algebraic locus for raw prefix recovery",
        H("Generic recovery in the actual open-boundary MPS image"),
        Blocks(
            Definition("realCoordinates", "Real coordinates of complex amplitudes",
                "The two copies of the index set contain the real and imaginary parts, with values in the real numbers. This coordinate map is distinct from PhasePolynomial.cartesian, whose values and polynomial coefficient field remain complex."),
            Describe.Lean(DescribeId.Create("density-genericity-continuous-real-coordinates"),
                DeclarationHandle.Create(Module + ".continuous_realCoordinates"),
                H("Continuity of full real and imaginary amplitude coordinates"),
                StatementSource.FromAuthor(All("iota", X("Type"),
                    At("Continuous", At("realCoordinates", X("iota"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The coordinate map from iota-indexed complex amplitudes to the two real coordinate copies is continuous for every index type. Continuity is proved coordinatewise and applies in particular to physical-mass-one normalization."))),
                DescribeRole.Theorem),
            Definition("transferMatrix", "The four-entry transfer matrix",
                "Rows and columns are indexed by pairs of bond indices. The (i,j),(k,l) entry is the sum over the two physical symbols of A_s(i,k) times the conjugate of A_s(j,l). Matrix multiplication on the flattened four complex entries is exactly the original transfer operator. Its determinant is nonzero precisely when that complex linear transfer is injective."),
            Definition("numeratorTransfer", "Polynomial transfer numerators",
                "Reuse matrixNumerator from the original Cramer reconstruction. Its first entry factor uses the t variables; the second uses independent conjugate-t variables and coefficient conjugation. The determinant is therefore a polynomial before imposing actual conjugacy. No second Cramer construction or rational parameter map is introduced."),
            Definition("recoveryPolynomial", "One polynomial with real coefficients",
                "Multiply the original chartPoly by the numerator-transfer determinant in independent t and conjugate-t variables. Apply the existing PhasePolynomial.toCartesian. Split the resulting coefficients into their real and imaginary parts and add the squares of the two real polynomials. Evaluation is exactly the complex norm square of the original product. Complex real and imaginary parts are used as additive coefficient maps, never as ring homomorphisms."),
            Describe.Lean(DescribeId.Create("recovery-polynomial-nonzero"),
                DeclarationHandle.Create(Module + ".recoveryPolynomial_ne_zero"),
                H("Exact polynomial characterization of the reconstruction conditions"),
                StatementSource.FromAuthor(Disp(PolynomialCondition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On the coherent chart, the original chart_scalars formula identifies each reconstructed matrix with c times its matrixNumerator evaluation, where c is nonzero. Consequently the transfer matrix is multiplied by c times its conjugate, and the four-dimensional determinant by its fourth power. The exact norm-square evaluation proves the displayed equivalence. This fixed-selector condition is sufficient for ObservableChart; no equivalence with its existential selector is asserted."))),
                DescribeRole.Theorem),
            Definition("fixedTensor", "The fixed observed column",
                "For the all-zero three-bit word e, retain Q at column e. Equivalently this is Q times the standard basis vector at e. The selector is fixed and depends on no unknown MPS parameters."),
            Definition("observedPolynomial", "A principal condition in observed density coordinates",
                "Rename the variables of recoveryPolynomial into the real and imaginary coordinates of the e column of the full observed Q3 matrix. Thus this is a literal real multivariate polynomial in observed entries, supported on sixteen real coordinates. It is not an analyticity-only or parameter-open condition."),
            Definition("statePolynomial", "The quadratic raw-density substitution",
                "Substitute the real and imaginary parts of Q3(psi) at its fixed column into recoveryPolynomial. The real coordinate is the complement sum of real-real plus imaginary-imaginary products; the imaginary coordinate is imaginary-real minus real-imaginary. This polynomial evaluates exactly to observedPolynomial on the actual raw Hermitian prefix density of every complex amplitude function, without an MPS hypothesis."),
            Definition("parameterPolynomial", "Pullback through the original MPS parametrization",
                "Substitute the Cartesian real and imaginary parts of the existing parameterPolys into statePolynomial. The result has real coefficients on the original twelve complex, hence twenty-four real, matrix-and-boundary coordinates. The proof uses the supplier parameter_eval and parameter_image with their original telescopes."),
            Definition("goodStates", "The intrinsic relative principal open set",
                "The source is the subtype of the literal parametrized image openBoundaryMPS(3+m), not its Zariski closure. A state belongs exactly when observedPolynomial evaluated on the real and imaginary entries of its raw first-three-site density is nonzero. The statePolynomial pullback proves relative Euclidean openness; the displayed observed polynomial supplies the real-algebraic presentation."),
            Describe.Lean(DescribeId.Create("intrinsic-recovery-genericity"),
                DeclarationHandle.Create(Module + ".intrinsic_recovery_genericity"),
                H("Nonempty dense actual-image generic recovery at every length"),
                StatementSource.FromAuthor(Disp(Genericity())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural complement length m, goodStates m is nonempty, open and dense in the subtype topology of the actual free-boundary state image. In particular this covers every original length N=3+m at least four. Every target in this locus is recovered up to a unit complex phase against every actual competitor. The competitor carries no genericity, coherent-chart or regular-parameter premise. The observation is the source's raw prefix Q3, with affine scale retained.")),
                    Paragraph(Text("The uniform actual witness uses the original A0=[[1,2],[3,4]], A1=[[5,6],[7,8]], l=(1,0), r=(1,2). Its fixed observed coherent vector has effective boundary E^m(rr-dagger) times (37,54). The real symmetric tail entries a,b,c stay strictly positive under the exact recurrence (26a+64b+40c,38a+92b+56c,58a+136b+80c). The effective boundary is (37a+54b,37b+54c). The original positive-boundary chart theorem applies directly. Exact linear combinations of the four output entries certify injectivity of the original transfer. The reused three-site gauge preserves transfer injectivity by invertible conjugate sandwiches and a nonzero scalar. This density-column witness is distinct from the coherent sum-tail used in the minimality supplier.")),
                    Paragraph(Text("The real polynomial parameter pullback is nonzero at this actual witness. Multidimensional real analytic uniqueness makes its zero locus have empty interior in the full connected real parameter space. Continuity of the original polynomial MPS map sends every parameter value into the closure of the image of good parameters. The exact pullback identities put that image inside goodStates. This proves density in the actual state image without assuming the MPS map is open, or identifying its Euclidean image with a complex Zariski closure.")),
                    Paragraph(Text("The existing observable_chart_phase_recovery supplies the final arbitrary-competitor unit-phase equivalence. The gauge and coherent reconstruction are due to the original Conjecture 8 supplier, including the Ma-Zhang canonical inverse. This is the recovery-genericity portion of the prefix reading of Conjecture 9. Generic-point two-site minimality in the full actual state image is not established by this recovery theorem; the separate canonical-parameter open collision theorem does not supply that descent. No Conjecture 9 resolution, all-interior-window theorem, normalized-state theorem, physical inverse, stability, dynamics or thermodynamic assertion is made."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("density-genericity-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PolynomialCondition()
    {
        var t = X("t");
        var left = Ne(At("MvPolynomial.eval", At("realCoordinates", t), At("recoveryPolynomial")), D(0));
        var right = And(Ne(At("MvPolynomial.eval", t, At("OpenBoundaryMPSMarginalBirationality.chartPoly")), D(0)),
            At("Function.Injective", At("OpenBoundaryMPSDensityRecovery.transfer",
                At("OpenBoundaryMPSDensityRecovery.canonicalCore", t))));
        return All("t", Arrow(At("Word", D(3)), Complex), Iff(left, right));
    }

    private static Formula Genericity()
    {
        var m = X("m"); var p = X("psi"); var q = X("phi"); var z = X("z");
        var n = new Formula.Binary(D(3), FormulaBinaryOperator.Add, m);
        var state = Arrow(At("Word", n), Complex);
        var model = At("OpenBoundaryMPSMarginalBirationality.openBoundaryMPS", n);
        var good = At("goodStates", m);
        var raw = Eq(At("OpenBoundaryMPSDensityRecovery.rawPrefix", D(3), m, q),
            At("OpenBoundaryMPSDensityRecovery.rawPrefix", D(3), m, At("Subtype.val", p)));
        var phase = Some("z", Complex, And(Eq(At("norm", z), D(1)), Eq(q, At("smul", z, At("Subtype.val", p)))));
        var recovery = All("psi", At("Subtype", model), Imp(Member(p, good),
            All("phi", state, Imp(Member(q, model), Iff(raw, phase)))));
        return All("m", Nat, And(At("Nonempty", good), At("IsOpen", good), At("Dense", good), recovery));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Complex => Seq(Mathbb, Grp(X("C")));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula At(string name, params Formula[] args)
    {
        var parts = name.Split('.'); var items = new List<Formula>();
        foreach (var part in parts) { if (items.Count > 0) items.Add(Dot); items.Add(X(part)); }
        return new Formula.Apply(Seq(Operatorname, Grp(Seq([.. items]))), [.. args]);
    }
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Imp(Formula a, Formula b) => Arrow(Par(a), Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula And(params Formula[] fs) => fs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
}
