using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorCommonCoreDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual raw interior three-site observation gives conditional full-state phase recovery against every actual bond-two competitor, using target-only spanning, positive definite actual environments and injective transfer.",
        H("Interior observations, a common core and phase recovery"),
        Blocks(
            Definition("interiorColumns", "Both actual exterior words",
                "For a state of length (p+k)+q, row u and column (a,b) contain the actual amplitude at append(append(a,u),b). Neither exterior is shifted, identified or summed coherently."),
            Definition("rawInterior", "Raw interior Hermitian density",
                "The observation is C C† for these interior amplitude columns. It is unnormalized, preserves the norm-squared scale, and differs from the raw prefix observation and the coherent improper marginal."),
            Definition("feature", "Transposed trace coordinates",
                "The feature entry F(u,(i,j)) is A_u(j,i). Therefore F times the coordinate vector X(i,j) is gamma A k X, where gamma is the original trace(X A_u). No conjugation is applied to X."),
            Definition("context", "Actual left and right contexts",
                "K((i,j),(a,b))=(A_b r)(i)(l A_a)(j), with bilinear row l. The corresponding virtual coefficient is A_b (r l) A_a. Matrix multiplication gives C=F K for every actual realization, including singular competitors."),
            Definition("dualTransfer", "The left environment transfer",
                "The map sends X to the sum of A_i† X A_i. Write P=(dualTransfer A)^p(l†l), H=(transfer A)^q(rr†). Snoc induction over original words gives prefixMap† prefixMap=P; the original right tail_gram supplies H. The finite context dictionary is K K†=H tensor P-transpose, and the exact observed density is F (H tensor P-transpose) F†. The transpose and the order of the two exterior words are essential."),
            Theorem("left_boundary_gram", "The actual left Gram dictionary", LeftGramFormula(),
                "For every finite p, prefixMap dagger times prefixMap is the p-fold dual transfer of the actual bilinear boundary Gram. This is the original snoc-induction supplier, exposed with its proof unchanged for the root-realization consumer; it is not new mathematics in that consumer."),
            Theorem("interior_density_dictionary", "The entire actual interior Gram dictionary", DictionaryFormula(),
                "For every finite p,k,q, rawInterior is feature times the Kronecker product of the right environment and transposed left environment times feature dagger. The original proof is unchanged. The root-realization consumer specializes k=2 while retaining all exterior words and all raw matrix entries."),
            Theorem("all_coefficient_parent_induction", "Every virtual coefficient propagates", InductionFormula(),
                "For arbitrary A,B with TwoSiteSpanning A, assume every three-site gamma B 3 X belongs to the target gamma image. For every natural m and every complex two by two X, there is Y with gamma B (m+3) X=gamma A (m+3) Y. The induction generalizes X. Its snoc branch uses B_j X through trace cyclicity, its cons branch uses X B_i. Both slices belong to the same actual function gamma B (m+4) X, so the original unrestricted parent_intersection applies. The statement imposes no physical cyclicity, shifted marginal or competitor regularity."),
            Theorem("interior_common_core", "A common core for every actual competitor", CommonCoreFormula(),
                "Let p,q be at least one and N=(p+3)+q. Only the target A satisfies TwoSiteSpanning and positive definiteness of P,H. The competitor B and its two free boundaries are entirely arbitrary. Equality of their raw interior observations implies that the entire actual competitor state is gamma A N X for one unrestricted complex two by two coefficient X. No transfer inverse, common-core premise, coefficient-image equality, rank-one premise or regularity of B is assumed."),
            Theorem("common_core_rank_one", "Rank-one obstruction for an actual common core", RankOneFormula(),
                "Let N be at least four and suppose an actual free-boundary binary bond-two competitor equals gamma A N X for a TwoSiteSpanning target core A. The weighted two-site flattening of gamma A N X is a submatrix of the competitor's amplitude-column matrix, so its rank is at most two. If X were invertible, left multiplication by X would preserve the four-dimensional two-site span and give rank four, a contradiction. Hence rank X is at most one, including X=0; the existing rank-one factorization and the private state-gamma identity then refactor the same competitor through A with arbitrary new boundaries. This adds no transfer, positivity, phase, genericity, dynamical or thermodynamic premise."),
            Theorem("interior_phase_recovery", "Conditional interior phase recovery for arbitrary competitors", PhaseFormula(),
                "Let p,q be at least one and N=(p+3)+q. Assume only the target core A has TwoSiteSpanning and injective complex-linear transfer, with its actual P,H positive definite. For arbitrary competitor core B and arbitrary free boundaries lprime,rprime, equality of the entire unnormalized rawInterior p 3 q matrices implies that the actual full competitor is z times the target for one complex z of norm one. The proof first uses interior_common_core and common_core_rank_one without altering their statements. No same-core, rank-one or competitor regularity premise is added to this endpoint."),
            Paragraph(Text("After refactorization through A, cancel F W F† using a private sandwich lemma with four columns indexed by Fin 2 times Fin 2; the original two-column sandwich lemma cannot apply here. The dictionary gives W=H tensor P-transpose, with entry H(i,k) P(t,j). Scalar linearity and transfer injectivity cancel the q-fold right iterate. The bilinear trace identity trace(Y E(X))=trace(Edual(Y) X), finite-dimensional surjectivity of E, and trace extensionality give injectivity of Edual, so the p-fold left iterate cancels as well. No positivity, p≥1 or q≥1 is used within this same-core phase argument.")),
            Paragraph(Text("The resulting entries are precisely equality of the outer Grams of the flattened coefficients x(i,j)=r(i)l(j). A consumed private dimension-generic version of the original boundary_phase argument handles x=0 before selecting a nonzero coordinate, and gives xhat=z x with norm(z)=1. The unchanged state-gamma identity and trace linearity propagate z to the entire state. This preserves the bilinear left boundary and the P transpose; no reciprocal positive factors, square roots or positivity of competitor environments are required.")),
            Paragraph(Text("Positive definiteness makes det(H tensor P-transpose) nonzero by the existing Kronecker determinant theorem. The context has full row rank four. Original trace_separates makes the target three-site feature injective, hence the observed column range is precisely the four-dimensional target parent space. Original gram_range transfers this range to the competitor. Its observed dimension four saturates the entire competitor coefficient image, whose dimension is at most four; this establishes the all-coefficient induction hypothesis. Apply that induction at m=p+q and coefficient r′ l′ to obtain the actual full competitor.")),
            Paragraph(Text("The rank-one result is conditional on the already established common-core representation and N≥4. It is a coefficient-rank statement for actual free-boundary points; it does not by itself recover the boundary phase, prove transfer injectivity, extend to the closure of the MPS image, or settle Critch–Morton Conjecture 9.")),
            Paragraph(Text("The theorem interior_common_core alone supplies the common-core representation; common_core_rank_one now proves rank X≤1 and free-boundary refactorization under N≥4 and TwoSiteSpanning A. Conditional interior phase recovery is supplied by interior_phase_recovery; intrinsic interior genericity and Critch–Morton Conjecture 9 remain unproved, and this unit earns no solved-open-problem credit. The imported Conjecture 8 canonical reconstruction remains attributed to Haobo Ma and Wenlin Zhang, Proof of Critch–Morton Conjecture 8 (3 November 2026), CC BY 4.0; it is not new interior recovery mathematics. No normalization, physical recovery operation, dynamics, time group, energy, clock or thermodynamic cost is asserted.")))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("interior-core-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("interior-core-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula LeftGramFormula()
    {
        var a = X("A"); var l = X("l"); var p = X("p");
        var prefix = At(Supplier("OpenBoundaryMPSDensityRecovery", "prefixMap"), a, l, p);
        var target = At(Q("Function", "iterate"), At(Local("dualTransfer"), a), p,
            At(Q("Matrix", "vecMulVec"), At(Q("star"), l), l));
        var gram = At(Q("Matrix", "mul"), At(Q("Matrix", "conjTranspose"), prefix), prefix);
        return Disp(All("A", Core(), All("l", Boundary(), All("p", Nat(), Eq(gram, target)))));
    }
    private static Formula DictionaryFormula()
    {
        var a = X("A"); var l = X("l"); var r = X("r");
        var p = X("p"); var k = X("k"); var q = X("q");
        var n = Add(Add(p, k), q);
        var feature = At(Local("feature"), a, k);
        var left = At(Q("Function", "iterate"), At(Local("dualTransfer"), a), p,
            At(Q("Matrix", "vecMulVec"), At(Q("star"), l), l));
        var right = At(Q("Function", "iterate"), At(Supplier("OpenBoundaryMPSDensityRecovery", "transfer"), a), q,
            At(Q("Matrix", "vecMulVec"), r, At(Q("star"), r)));
        var middle = At(Q("Matrix", "kronecker"), right, At(Q("Matrix", "transpose"), left));
        var sandwich = At(Q("Matrix", "mul"), At(Q("Matrix", "mul"), feature, middle),
            At(Q("Matrix", "conjTranspose"), feature));
        return Disp(All("A", Core(), All("l", Boundary(), All("r", Boundary(),
            All("p", Nat(), All("k", Nat(), All("q", Nat(),
            Eq(At(Local("rawInterior"), p, k, q, State(a, l, r, n)), sandwich))))))));
    }
    private static Formula InductionFormula()
    {
        Formula a = X("A"), b = X("B"), m = X("m"), x = X("X"), y = X("Y");
        Formula seed = All("X", Bond(), Some("Y", Bond(), Eq(G(b, D(3), x), G(a, D(3), y))));
        Formula n = Add(m, D(3));
        return Disp(All("A", Core(), All("B", Core(), Imp(Spanning(a), Imp(seed,
            All("m", Nat(), All("X", Bond(), Some("Y", Bond(), Eq(G(b, n, x), G(a, n, y))))))))));
    }
    private static Formula CommonCoreFormula()
    {
        Formula a = X("A"), b = X("B"), l = X("l"), r = X("r"), lp = X("lprime"), rp = X("rprime");
        Formula p = X("p"), q = X("q"), n = Add(Add(p, D(3)), q);
        Formula target = State(a, l, r, n), competitor = State(b, lp, rp, n);
        Formula left = At(Q("Function", "iterate"), At(Local("dualTransfer"), a), p,
            At(Q("Matrix", "vecMulVec"), At(Q("star"), l), l));
        Formula right = At(Q("Function", "iterate"), At(Supplier("OpenBoundaryMPSDensityRecovery", "transfer"), a), q,
            At(Q("Matrix", "vecMulVec"), r, At(Q("star"), r)));
        Formula raw = Eq(At(Local("rawInterior"), p, D(3), q, competitor), At(Local("rawInterior"), p, D(3), q, target));
        Formula result = Some("X", Bond(), Eq(competitor, G(a, n, X("X"))));
        return Disp(All("A", Core(), All("B", Core(), All("l", Boundary(), All("r", Boundary(),
            All("lprime", Boundary(), All("rprime", Boundary(), All("p", Nat(), All("q", Nat(),
            Imp(Le(D(1), p), Imp(Le(D(1), q), Imp(Spanning(a),
            Imp(At(Q("Matrix", "PosDef"), left), Imp(At(Q("Matrix", "PosDef"), right), Imp(raw, result)))))))))))))));
    }
    private static Formula PhaseFormula()
    {
        Formula a = X("A"), b = X("B"), l = X("l"), r = X("r"), lp = X("lprime"), rp = X("rprime");
        Formula p = X("p"), q = X("q"), z = X("z"), n = Add(Add(p, D(3)), q);
        Formula target = State(a, l, r, n), competitor = State(b, lp, rp, n);
        Formula transfer = At(Supplier("OpenBoundaryMPSDensityRecovery", "transfer"), a);
        Formula left = At(Q("Function", "iterate"), At(Local("dualTransfer"), a), p,
            At(Q("Matrix", "vecMulVec"), At(Q("star"), l), l));
        Formula right = At(Q("Function", "iterate"), transfer, q,
            At(Q("Matrix", "vecMulVec"), r, At(Q("star"), r)));
        Formula raw = Eq(At(Local("rawInterior"), p, D(3), q, competitor), At(Local("rawInterior"), p, D(3), q, target));
        Formula phase = Some("z", Seq(Mathbb, Grp(X("C"))), And(Eq(At(Q("norm"), z), D(1)),
            Eq(competitor, At(Q("HSMul", "hSMul"), z, target))));
        Formula premise = Imp(Le(D(1), p), Imp(Le(D(1), q), Imp(Spanning(a),
            Imp(At(Q("Function", "Injective"), transfer), Imp(At(Q("Matrix", "PosDef"), left),
            Imp(At(Q("Matrix", "PosDef"), right), Imp(raw, phase)))))));
        return Disp(All("A", Core(), All("B", Core(), All("l", Boundary(), All("r", Boundary(),
            All("lprime", Boundary(), All("rprime", Boundary(), All("p", Nat(), All("q", Nat(), premise)))))))));
    }
    private static Formula RankOneFormula()
    {
        Formula a = X("A"), b = X("B"), lp = X("lprime"), rp = X("rprime");
        Formula n = X("N"), x = X("X"), la = X("lA"), ra = X("rA");
        Formula competitor = State(b, lp, rp, n);
        Formula target = State(a, la, ra, n);
        Formula factor = And(Eq(x, At(Q("Matrix", "vecMulVec"), ra, la)), Eq(competitor, target));
        Formula result = And(Le(At(Q("Matrix", "rank"), x), D(1)), Some("lA", Boundary(),
            Some("rA", Boundary(), factor)));
        Formula premise = Eq(competitor, G(a, n, x));
        return Disp(All("A", Core(), All("B", Core(), All("lprime", Boundary(),
            All("rprime", Boundary(), All("N", Nat(), All("X", Bond(),
            Imp(Le(D(4), n), Imp(Spanning(a), Imp(premise, result))))))))));
    }
    private static Formula State(Formula a, Formula l, Formula r, Formula n) =>
        At(Supplier("OpenBoundaryMPSMarginalBirationality", "mpsState"), n, At(a, D(0)), At(a, D(1)), l, r);
    private static Formula G(Formula a, Formula n, Formula x) => At(Supplier("PeriodicMPSParentIntersection", "gamma"), a, n, x);
    private static Formula Spanning(Formula a) => At(Supplier("PeriodicMPSParentIntersection", "TwoSiteSpanning"), a);
    private static Formula Bond() => Supplier("PeriodicMPSParentIntersection", "Bond");
    private static Formula Core() => new Formula.TypeArrow(At(Q("Fin"), D(2)), Bond());
    private static Formula Boundary() => new Formula.TypeArrow(At(Q("Fin"), D(2)), Seq(Mathbb, Grp(X("C"))));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula X(string x) => F.Id(x);
    private static Formula Q(params string[] names)
    {
        var parts = new List<Formula>();
        foreach (var name in names) { if (parts.Count > 0) parts.Add(Dot); parts.Add(X(name)); }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Supplier(string module, string name) => Q("D5", "S3", "Quantum", "TensorNetworks", module, name);
    private static Formula Local(string name) => Supplier("OpenBoundaryMPSInteriorCommonCore", name);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula t, Formula f) => Seq(Forall, Sp, Par(Seq(X(x), Colon, Sp, t)), Comma, Sp, Par(f));
    private static Formula Some(string x, Formula t, Formula f) => Seq(F.Exists, Sp, Par(Seq(X(x), Colon, Sp, t)), Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(params Formula[] fs) => fs.Aggregate((a, b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
}
