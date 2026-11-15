using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorCommonCoreDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual raw interior three-site observation with positive definite target environments forces every actual bond-two competitor into the target's full-length parent space.",
        H("Interior observations and a common virtual core"),
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
            Theorem("all_coefficient_parent_induction", "Every virtual coefficient propagates", InductionFormula(),
                "For arbitrary A,B with TwoSiteSpanning A, assume every three-site gamma B 3 X belongs to the target gamma image. For every natural m and every complex two by two X, there is Y with gamma B (m+3) X=gamma A (m+3) Y. The induction generalizes X. Its snoc branch uses B_j X through trace cyclicity, its cons branch uses X B_i. Both slices belong to the same actual function gamma B (m+4) X, so the original unrestricted parent_intersection applies. The statement imposes no physical cyclicity, shifted marginal or competitor regularity."),
            Theorem("interior_common_core", "A common core for every actual competitor", CommonCoreFormula(),
                "Let p,q be at least one and N=(p+3)+q. Only the target A satisfies TwoSiteSpanning and positive definiteness of P,H. The competitor B and its two free boundaries are entirely arbitrary. Equality of their raw interior observations implies that the entire actual competitor state is gamma A N X for one unrestricted complex two by two coefficient X. No transfer inverse, common-core premise, coefficient-image equality, rank-one premise or regularity of B is assumed."),
            Paragraph(Text("Positive definiteness makes det(H tensor P-transpose) nonzero by the existing Kronecker determinant theorem. The context has full row rank four. Original trace_separates makes the target three-site feature injective, hence the observed column range is precisely the four-dimensional target parent space. Original gram_range transfers this range to the competitor. Its observed dimension four saturates the entire competitor coefficient image, whose dimension is at most four; this establishes the all-coefficient induction hypothesis. Apply that induction at m=p+q and coefficient r′ l′ to obtain the actual full competitor.")),
            Paragraph(Text("This intermediate common-core result does not establish a rank-one coefficient, phase recovery, intrinsic genericity, or Critch–Morton Conjecture 9 and earns no solved-open-problem credit. The imported Conjecture 8 canonical reconstruction remains attributed to Haobo Ma and Wenlin Zhang, Proof of Critch–Morton Conjecture 8 (3 November 2026), CC BY 4.0; it is not new interior recovery mathematics. No normalization, physical recovery operation, dynamics, time group, energy, clock or thermodynamic cost is asserted.")))));

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
}
