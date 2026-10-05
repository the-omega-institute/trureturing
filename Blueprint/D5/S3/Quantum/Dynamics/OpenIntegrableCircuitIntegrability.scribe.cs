using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OpenIntegrableCircuitIntegrabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quantum/garciafernandez2026openqc");
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula MatrixEquivalence() => Seq(Qualified("LinearMap", "toMatrixAlgEquiv"), Apos);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Type() => V("Type");
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula PlusTo(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesTo(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negative(Formula a) => new Formula.Negate(a);
    private static Formula AndTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula OrTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Conjoin(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) result = AndTo(clauses[i], result);
        return result;
    }
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula ProductType(Formula a, Formula b) => Seq(a, Sp, F.Times, Sp, b);
    private static Formula MatrixType(Formula a) => Call("Matrix", a, a, Complexes());
    private static Formula Bracket(string instance, Formula type) => Seq(OpenBracket, Call(instance, type), CloseBracket, Sp);
    private static Formula Instances(Formula body, bool finiteSites = true, bool equalSites = true, bool finiteLocal = true, bool equalLocal = true)
    {
        Formula sites = V("Sites"), local = V("Local");
        return Seq(finiteSites ? Bracket("Fintype", sites) : Sp,
            equalSites ? Bracket("DecidableEq", sites) : Sp,
            finiteLocal ? Bracket("Fintype", local) : Sp,
            equalLocal ? Bracket("DecidableEq", local) : Sp, body);
    }
    private static Formula Generic(Formula body) => All("Sites", Type(), All("Local", Type(), body));
    private static Formula SumOver(string index, Formula type, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(V(index), Sp, InMacro, Sp, type)), Sp, body);
    private static Formula ProductOver(string index, Formula type, Formula body) => Seq(new Formula.Subscript(Prod, Seq(V(index), Sp, InMacro, Sp, type)), Sp, Parenthesized(body));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula LocalDimension() => FinOf(V("D"));
    private static Formula Sites() => FinOf(PlusTo(V("N"), D(1)));
    private static Formula SpectralRType() => Arrow(Complexes(), Arrow(Complexes(), MatrixType(ProductType(LocalDimension(), LocalDimension()))));
    private static Formula BoundaryType() => Arrow(Complexes(), MatrixType(LocalDimension()));
    private static Formula Model(Formula body) => All("N", Naturals(), All("D", Naturals(), All("R", SpectralRType(),
        All("KR", BoundaryType(), All("KL", BoundaryType(), body)))));
    private static Formula Transfer(Formula u, Formula theta) => Call("transfer", V("N"), V("D"), V("R"), V("KR"), V("KL"), u, theta);
    private static Formula Gate(Formula i) => Call("gate", V("N"), V("D"), V("R"), V("KR"), V("KL"), V("kappa"), i);
    private static Formula Circuit() => Call("circuitProduct", V("N"), V("D"), V("R"), V("KR"), V("KL"), V("kappa"), V("pi"));
    private static Formula ScalarTimes(Formula c, Formula a) => Call("smul", c, a);
    private static Formula P(Formula local) => Apply(Qualified("PEquiv", "toMatrix"),
        Apply(Qualified("Equiv", "toPEquiv"), Apply(Qualified("Equiv", "prodComm"), local, local)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every ordering that uses each boundary gate and each nearest-neighbour gate once is a nonzero scalar multiple of a double-row transfer matrix with signed inhomogeneities. Mutual commutation of the transfer matrices implies commutation of the circuit with that family.",
        H("All gate orderings of an open-boundary transfer-matrix circuit"), Blocks(
            Node("oneOp", "One-site embedding", OneFormula(),
                "The matrix acts at site i. The update operation replaces only that coordinate of the configuration; the sum ranges over every local basis label.", true),
            Node("twoOp", "Oriented two-site embedding", TwoFormula(),
                "The first and second components of p replace sites i and j respectively. All other coordinates remain fixed.", true),
            Node("checkedR", "The checked matrix", All("Local", Type(), Seq(Bracket("Fintype", V("Local")), Bracket("DecidableEq", V("Local")),
                All("R", MatrixType(ProductType(V("Local"), V("Local"))), EqTo(Call("checkedR", V("R")), TimesTo(P(V("Local")), V("R")))))),
                "The source defines the checked matrix as P R. Here P is PEquiv.toMatrix applied to Equiv.toPEquiv of Equiv.prodComm, whose entry at (x,y) is one exactly when swapping the two components of x gives y.", true),
            Node("partialTrace", "Trace over the auxiliary factor", TraceFormula(),
                "The auxiliary site is none, and physical sites are some i. Equiv.piOptionEquivProd identifies a configuration on Option Sites with its auxiliary label and physical configuration. LinearMap.toMatrixAlgEquiv' is the forward map over the complex numbers; its .symm is the inverse map. Matrix.reindex uses this configuration equivalence for both indices. partialTraceLeft is the existing matrix trace over the first factor, without normalization.", false),
            Node("leftGate", "The left boundary gate", LeftFormula(),
                "The source's left gate is the auxiliary trace of K-a-L times P-a-p R-p-a. Embedding checkedR on the oriented pair (p,a) gives precisely that product because the swap is symmetric.", true),
            Node("transfer", "The explicit double-row transfer matrix", TransferFormula(),
                "The first product is ordered N down to 0 and the second 0 up to N. The source's chain length is N + 1, and its physical site i + 1 is encoded by i. The products are the explicit R-matrix products, and no inverse monodromy is introduced.", true),
            Node("gate", "The bulk and boundary gate family", GateFormula(),
                "The gate at label zero is the right boundary matrix at physical site zero. Labels 1 through N carry the checked bulk matrix, and label N + 1 is the auxiliary-traced left boundary matrix. Fin.ofNat supplies the site indices; on 0 through N these have their ordinary values.", true),
            Node("circuitProduct", "A once-per-label ordering", CircuitFormula(),
                "The permutation runs over all N + 2 labels, including both boundary gates. A product indexed by Fin uses increasing val order, namely List.ofFn followed by List.prod. It follows the permutation's operator-product order. val extracts the natural label of an element of Fin.", true),
            Node("claim", "The open-boundary integrability conjecture", Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))),
                "Section 3.1.2, p. 15: “For the open-boundary case, similarly to the periodic setting [31], we conjecture that any circuit in which each gate U_{i,i+1} (constructed from an Ř-matrix) appears exactly once per period to every nearest-neighbor pair of spins, and where each boundary gate is constructed from a K-matrix, is integrable.” The encoding uses N + 1 physical sites and N + 2 gates, so 1 <= N is exactly the source's chain length at least two. R, KR and KL are arbitrary matrix-valued spectral functions. Regularity and the two nonzero scalar values suffice for the identity. smul denotes the complex scalar action. Integrability is the conditional commutation statement using the source's standing transfer-commutation property, equation (12); deriving that property from Yang–Baxter and reflection equations is separate.", true),
            Describe.Lean(DescribeId.Create("openqc-integrability-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Every ordering has a transfer-matrix realization"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Assign a negative inhomogeneity at physical site i - 1 exactly when label i precedes label i - 1 in the circuit word. Nonadjacent labels act on disjoint sites and commute. Sorting the labels by the signed key gives the descending negative labels, then zero, then the ascending positive labels, without changing the product. The auxiliary swap train reduces the explicit double-row product to the reversed gate word of circuit, whose time order is fixed by the boundary and bulk gates. The induction uses that same gate word with the terminal KN gate removed; K1 represents label zero and U j represents label j. Each regular checked matrix supplies a scalar identity; their nonzero product accounts for the proportionality constant. Both terminal signs give the same correspondence. Finally a scalar multiple of the transfer matrix at kappa commutes with the transfer family whenever that family mutually commutes."))), DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("openqc-integrability-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula OneFormula()
    {
        Formula sites = V("Sites"), local = V("Local"), i = V("i"), b = V("B"), f = V("f"), x = V("x"), p = V("p");
        return Generic(Instances(All("i", sites, All("B", MatrixType(local),
            All("f", Arrow(Arrow(sites, local), Complexes()), All("x", Arrow(sites, local),
                EqTo(Apply(Call("oneOp", i, b), f, x), SumOver("p", local,
                    TimesTo(Apply(b, Apply(x, i), p), Apply(f, Call("update", x, i, p))))))))), false, true, true, false));
    }
    private static Formula TwoFormula()
    {
        Formula sites = V("Sites"), local = V("Local"), i = V("i"), j = V("j"), r = V("R"), f = V("f"), x = V("x"), p = V("p");
        Formula update = Call("update", Call("update", x, i, Call("fst", p)), j, Call("snd", p));
        Formula entry = Apply(r, Pair(Apply(x, i), Apply(x, j)), p);
        Formula identity = EqTo(Apply(Call("twoOp", i, j, r), f, x),
            SumOver("p", ProductType(local, local), TimesTo(entry, Apply(f, update))));
        Formula binders = All("i", sites, All("j", sites, All("R", MatrixType(ProductType(local, local)),
            All("f", Arrow(Arrow(sites, local), Complexes()), All("x", Arrow(sites, local), identity)))));
        return Generic(Instances(binders, false, true, true, false));
    }
    private static Formula TraceFormula()
    {
        Formula sites = V("Sites"), local = V("Local"), f = V("F"), e = Apply(Qualified("Equiv", "piOptionEquivProd"), sites, local);
        return Generic(Instances(All("F", Call("End", Complexes(), Arrow(Arrow(Call("Option", sites), local), Complexes())),
            EqTo(Call("partialTrace", f), Apply(Seq(Parenthesized(MatrixEquivalence()), Dot, Named("symm")),
                Call("partialTraceLeft", Apply(Qualified("Matrix", "reindex"), e, e, Apply(MatrixEquivalence(), f))))))));
    }
    private static Formula LeftFormula()
    {
        Formula sites = V("Sites"), local = V("Local"), kl = V("KL"), p = V("p"), c = V("C");
        return Generic(Instances(All("KL", MatrixType(local), All("p", sites, All("C", MatrixType(ProductType(local, local)),
            EqTo(Call("leftGate", kl, p, c), Call("partialTrace", TimesTo(Call("oneOp", V("none"), kl),
                Call("twoOp", Call("some", p), V("none"), Call("checkedR", c))))))))));
    }
    private static Formula TransferFormula()
    {
        Formula i = V("i"), u = V("u"), theta = V("theta"), ei = Call("ofNat", PlusTo(V("N"), D(1)), i);
        Formula descending = Call("reverse", Call("range", PlusTo(V("N"), D(1)))), ascending = Call("range", PlusTo(V("N"), D(1)));
        Formula first = ProductOver("i", descending, Call("twoOp", V("none"), Call("some", ei), Apply(V("R"), u, Apply(theta, ei))));
        Formula second = ProductOver("i", ascending, Call("twoOp", Call("some", ei), V("none"), Apply(V("R"), Apply(theta, ei), Negative(u))));
        return Model(All("u", Complexes(), All("theta", Arrow(Sites(), Complexes()), EqTo(Transfer(u, theta),
            Call("partialTrace", TimesTo(TimesTo(TimesTo(Call("oneOp", V("none"), Apply(V("KL"), u)), first),
                Call("oneOp", V("none"), Apply(V("KR"), u))), second))))));
    }
    private static Formula GateFormula()
    {
        Formula i = V("i"), n = V("N"), k = V("kappa"), ei = Call("ofNat", PlusTo(n, D(1)), i), next = Call("ofNat", PlusTo(n, D(1)), PlusTo(i, D(1)));
        Formula bulk = Call("twoOp", ei, next, Call("checkedR", Apply(V("R"), k, Negative(k))));
        Formula left = Call("leftGate", Apply(V("KL"), k), Call("last", n), Apply(V("R"), k, Negative(k)));
        return Model(All("kappa", Complexes(), Conjoin(EqTo(Gate(D(0)), Call("oneOp", D(0), Apply(V("KR"), k))),
            All("i", Naturals(), EqTo(Gate(PlusTo(i, D(1))), Call("ite", EqTo(i, n), left, bulk))))));
    }
    private static Formula CircuitFormula() => Model(All("kappa", Complexes(), All("pi", Call("Perm", FinOf(PlusTo(V("N"), D(2)))),
        EqTo(Circuit(), ProductOver("i", FinOf(PlusTo(V("N"), D(2))), Gate(Call("val", Apply(V("pi"), V("i")))))))));
    private static Formula ClaimBody()
    {
        Formula k = V("kappa"), theta = V("theta"), c = V("c"), u = V("u"), v = V("v");
        Formula regular = All("u", Complexes(), EqTo(Apply(V("R"), u, u), ScalarTimes(Apply(V("g"), u), P(LocalDimension()))));
        Formula hypotheses = Conjoin(LeTo(D(1), V("N")), regular, NeTo(Apply(V("g"), k), D(0)), NeTo(Apply(V("g"), Negative(k)), D(0)));
        Formula family = All("u", Complexes(), All("v", Complexes(), Call("Commute", Transfer(u, theta), Transfer(v, theta))));
        Formula conclusion = ExistsIn("theta", Arrow(Sites(), Complexes()), ExistsIn("c", Complexes(), Conjoin(
            All("i", Sites(), OrTo(EqTo(Apply(theta, V("i")), k), EqTo(Apply(theta, V("i")), Negative(k)))),
            NeTo(c, D(0)), EqTo(Circuit(), ScalarTimes(c, Transfer(k, theta))),
            ImpliesTo(family, All("u", Complexes(), Call("Commute", Circuit(), Transfer(u, theta)))))));
        return Model(All("g", Arrow(Complexes(), Complexes()), All("kappa", Complexes(), ImpliesTo(hypotheses,
            All("pi", Call("Perm", FinOf(PlusTo(V("N"), D(2)))), conclusion)))));
    }
}
