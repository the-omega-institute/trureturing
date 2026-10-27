using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class TreeEndpointMomentCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.";
    public DocumentDefinition Create()
    {
        Formula k = V("K"), v = V("V"), g = V("G"), m = V("M"), jmat = V("J");
        Formula a = V("a"), c = V("c"), o = V("o"), z = V("z"), i = V("i"), j = V("j");
        Formula n = V("n"), r = V("r"), d = V("d"), p = V("p"), x = V("x");
        Formula affine = Field(All("a", k, All("c", k,
            Eqn(Call("affinePolynomial", a, c), Mul(Call("C", Inv(c)), Sub(Call("X"), Call("C", a)))))));
        Formula chain = Field(All("a", k, All("c", k, All("j", Nat(),
            Eqn(Call("chainPolynomial", a, c, j),
                Call("comp", Call("ChebyshevS", k, j), Call("affinePolynomial", a, c)))))));
        Formula polyvector = Data(All("M", Mat(v, k), All("o", v, All("p", Call("Polynomial", k),
            Eqn(Call("polynomialVector", m, o, p),
                Call("mulVec", Call("aeval", m, p), Call("unit", o)))))));
        Formula vector = StateData(Eqn(CV(m, o, a, c, j),
            Call("polynomialVector", m, o, Call("chainPolynomial", a, c, j))));
        Formula norm = StateData(Eqn(CN(m, o, a, c, j), Dot(CV(m, o, a, c, j), CV(m, o, a, c, j))));
        Formula positive = LinearlyOrdered(All("n", Nat(), All("J", Mat(Fin(n), k),
            Iff(Call("PositiveJacobi", jmat), Conj(Call("IsSymm", jmat),
                All("i", Fin(n), All("j", Fin(n), Imp(
                    Or(Lt(Add(Call("val", i), D(1)), Call("val", j)),
                        Lt(Add(Call("val", j), D(1)), Call("val", i))), Eqn(App(jmat, i, j), D(0))))),
                All("j", Nat(), Imp(Lt(Add(j, D(1)), n),
                    Lt(D(0), App(jmat, j, Add(j, D(1)))))))))));
        Formula unit = Field(All("n", Nat(), All("j", Nat(), All("i", Fin(n),
            Eqn(App(Call("unitAt", n, j), i), If(Eqn(Call("val", i), j), D(1), D(0)))))));
        Formula diagonal = Field(All("n", Nat(), All("J", Mat(Fin(n), k), All("j", Nat(),
            Eqn(Call("diagonalAt", jmat, j), If(Lt(j, n), App(jmat, j, j), D(0)))))));
        Formula link = Field(All("n", Nat(), All("J", Mat(Fin(n), k), All("j", Nat(),
            Eqn(Call("nextLink", jmat, j), If(Lt(Add(j, D(1)), n), App(jmat, j, Add(j, D(1))), D(0)))))));
        Formula stemNeighbors = Or(And(Lt(D(0), j), Eqn(x, GV(p, Sub(j, D(1))))),
            Eqn(x, GV(p, Add(j, D(1)))));
        Formula stem = BareGraph(All("o", v, All("z", v, All("p", Call("Walk", g, o, z),
            Iff(Call("IsStem", p), All("j", Nat(), Imp(Lt(j, Len(p)), All("x", v,
                Iff(Call("Adj", g, GV(p, j), x), stemNeighbors)))))))));
        Formula forward = Graph(All("o", v, All("z", v, All("p", Call("Walk", g, o, z),
            All("x", v, Iff(Call("mem", x, Call("forward", p)),
                And(Call("Adj", g, z, x), Or(Eqn(Len(p), D(0)),
                    Ne(x, Call("penultimate", p))))))))));
        Formula endpoint = BareGraph(All("o", v, Iff(Call("EndpointPath", g, o),
            Ex("n", Nat(), Ex("e", Call("GraphIso", g, Call("pathGraph", Add(n, D(1)))),
                Eqn(App(V("e"), o), D(0)))))));
        Formula uniform = Field(EqualityGraph(All("a", k, All("c", k,
            Eqn(Call("uniformMatrix", g, a, c), Add(Mul(a, Call("identity", v)),
                Mul(c, Call("adjMatrix", k, g))))))));
        Formula indicator = EqualityData(All("s", Call("Finset", v), All("x", v,
            Eqn(App(Call("indicatorVector", V("s")), x),
                If(Call("mem", x, V("s")), D(1), D(0))))));
        Formula pairingBody = Eqn(Dot(CV(m, o, a, c, i), CV(m, o, a, c, j)),
            Dot(CV(jmat, z, a, c, i), CV(jmat, z, a, c, j)));
        Formula pairing = TwoMatrices(All("d", Nat(), All("i", Nat(), All("j", Nat(),
            Imp(Moments(m, o, jmat, z, d), Imp(Le(Add(i, j), d), pairingBody))))));
        Formula diagBody = Eqn(Dot(CV(m, o, a, c, j), Call("mulVec", m, CV(m, o, a, c, j))),
            Dot(CV(jmat, z, a, c, j), Call("mulVec", jmat, CV(jmat, z, a, c, j))));
        Formula diag = TwoMatrices(All("d", Nat(), All("j", Nat(),
            Imp(Moments(m, o, jmat, z, d), Imp(Le(Add(Mul(D(2), j), D(1)), d), diagBody)))));
        Formula rigidResult = Conj(Le(r, n),
            All("j", Nat(), Imp(Lt(j, r), Eqn(Call("diagonalAt", jmat, j), a))),
            All("j", Nat(), Imp(Lt(Add(j, D(1)), r), Eqn(Call("nextLink", jmat, j), c))),
            Eqn(Dot(CV(jmat, D(0), a, c, r), CV(jmat, D(0), a, c, r)),
                Mul(Pow(Mul(Inv(c), Call("nextLink", jmat, Sub(r, D(1)))), D(2)),
                    If(Lt(r, n), D(1), D(0)))));
        Formula rigidUnit = All("j", Nat(), Imp(Lt(j, r),
            Eqn(Dot(CV(jmat, D(0), a, c, j), CV(jmat, D(0), a, c, j)), D(1))));
        Formula rigidDiagonal = All("j", Nat(), Imp(Lt(j, r),
            Eqn(Dot(CV(jmat, D(0), a, c, j), Call("mulVec", jmat, CV(jmat, D(0), a, c, j))), a)));
        Formula rigid = Ordered(All("n", Nat(), All("r", Nat(),
            Imp(Lt(D(0), n), Imp(Lt(D(0), r), All("J", Mat(Fin(n), k),
                Imp(Call("PositiveJacobi", jmat), All("a", k, All("c", k,
                    Imp(Lt(D(0), c), Imp(rigidUnit, Imp(rigidDiagonal, rigidResult))))))))))));
        Formula t = Call("uniformMatrix", g, a, c), len = Add(Len(p), D(1)), b = Card(Call("forward", p));
        Formula treeConclusion = Ex("z", v, Ex("p", Call("Walk", g, o, z), Conj(
            Call("IsPath", p), Call("IsStem", p), Le(D(1), len), Le(len, Card(v)),
            All("i", Nat(), Imp(Lt(i, len), All("j", Nat(), Imp(Lt(j, len),
                Eqn(Dot(CV(t, o, a, c, i), CV(t, o, a, c, j)), If(Eqn(i, j), D(1), D(0))))))),
            All("j", Nat(), Imp(Lt(j, len), Eqn(Dot(CV(t, o, a, c, j),
                Call("mulVec", t, CV(t, o, a, c, j))), a))),
            Eqn(CN(t, o, a, c, len), b), Or(Eqn(b, D(0)), Or(Eqn(b, D(2)), Eqn(b, D(3)))),
            Imp(Lt(D(0), Len(p)), Ne(b, D(3))),
            Imp(Eqn(b, D(0)), Ex("e", Call("GraphIso", g, Call("pathGraph", len)), Eqn(App(V("e"), o), D(0)))),
            All("j", Nat(), Imp(Lt(j, len), Eqn(CV(t, o, a, c, j), Call("unit", GV(p, j))))),
            Eqn(CV(t, o, a, c, len), Call("indicatorVector", Call("forward", p))))));
        Formula tree = OrderedGraph(Imp(Call("IsTree", g), Imp(
            All("x", v, Le(Call("degree", g, x), D(3))), All("o", v, All("a", k, All("c", k,
                Imp(Lt(D(0), c), treeConclusion)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual rooted finite tree recurrence states and every-order positive Jacobi rigidity.",
            H("Tree endpoint moment certificates"), Blocks(
                Paragraph(Text("The coefficient field is arbitrary where stated. Algebraic pairing needs only a field; positivity and the tree norm statements use a linearly ordered field. All vertices and the selected port belong to the same actual finite graph. No spectral, positivity, cyclicity, contraction or oracle premise is added to that graph.")),
                Node("affine", "The original spectral coordinate", "affinePolynomial", affine,
                    "Here X denotes the polynomial indeterminate and scalars denote constant polynomials. The formula is c inverse times (X minus a).", DescribeRole.Definition),
                Node("chain", "The fixed chain polynomials", "chainPolynomial", chain,
                    "Mathlib Chebyshev.S has S minus one equal to zero, S zero equal to one, and S at j plus one equal to X times S at j minus S at j minus one. Thus this is precisely the original Q recurrence composed with (z-a)/c; no polynomial is fitted to the observed graph.", DescribeRole.Definition),
                Node("polyvector", "Evaluation at the actual matrix", "polynomialVector", polyvector,
                    "Polynomial evaluation is in the matrix algebra; the resulting matrix acts on the selected unit coordinate.", DescribeRole.Definition),
                Node("vector", "Chain states", "chainVector", vector,
                    "The index is a natural number, beginning with the actual selected unit vector.", DescribeRole.Definition),
                Node("positive", "All positive symmetric Jacobi matrices", "PositiveJacobi", positive,
                    "Every natural order is allowed. The matrix is symmetric, entries farther than one from the diagonal vanish, and every existing adjacent link is strictly positive. The diagonals are unrestricted. The positive-order hypothesis is supplied only where an endpoint vector is needed.", DescribeRole.Definition),
                Node("unit", "Absent coordinates mean zero", "unitAt", unit,
                    "The zero extension lets the rigidity proof treat short, exact and larger matrix orders in the same recurrence.", DescribeRole.Definition),
                Node("diagonal", "Zero-extended diagonals", "diagonalAt", diagonal,
                    "The displayed entry uses its natural-number index only in the branch where that index is in range.", DescribeRole.Definition),
                Node("link", "Zero-extended links", "nextLink", link,
                    "There is no fictitious terminal link: the value is zero when its second endpoint is absent.", DescribeRole.Definition),
                Node("stem", "A locally saturated actual stem", "IsStem", stem,
                    "At every proper stem vertex, all actual neighbors are exactly the preceding vertex when present and the following vertex. This predicate alone does not assert existence; the tree theorem earns a simple path satisfying it.", DescribeRole.Definition),
                Node("forward", "The actual terminal boundary", "forward", forward,
                    "Only the incoming edge is removed. A zero-length stem removes no edge, so its forward boundary is the actual root's entire neighbor set.", DescribeRole.Definition),
                Node("endpoint", "Rooted endpoint paths", "EndpointPath", endpoint,
                    "A genuine graph isomorphism to a nonempty finite path sends the actual selected port to zero. This includes a singleton and excludes an interior port on a nontrivial path.", DescribeRole.Definition),
                Node("uniform", "The same actual graph law", "uniformMatrix", uniform,
                    "The adjacency matrix has unit edges and zero diagonal. The shift a is arbitrary, including zero and negative values.", DescribeRole.Definition),
                Node("norm", "Squared recurrence norms", "chainNorm", norm,
                    "Over the rationals this dot product is the exact sum of squares defining the squared Euclidean length; no square-root normalization is used.", DescribeRole.Definition),
                Node("indicator", "Actual boundary indicators", "indicatorVector", indicator,
                    "The value is one exactly on the given finite set of actual vertices.", DescribeRole.Definition),
                Node("pairing", "Moments determine the needed Gram entries", "prefix_chain_pairing", pairing,
                    "Expand matrix polynomial evaluation and use symmetry to identify the pairing of powers i and j with moment i+j. The degrees of the fixed chain polynomials are at most their indices. Equal moments through d therefore transfer every pairing with i+j at most d. This helper is consumed by the endpoint classification's prefix-rigidity step.", DescribeRole.Theorem),
                Node("diagpairing", "Moments determine the needed diagonal pairings", "prefix_chain_diagonal", diag,
                    "Apply the same polynomial pairing to p_j and X p_j. The total degree is at most 2j+1. This helper is consumed by the same prefix-rigidity step.", DescribeRole.Theorem),
                Node("rigidity", "Rigidity without an order bound", "positive_jacobi_prefix_rigidity", rigid,
                    "Inductively the required unit state forces the next coordinate to exist. Its positive coefficient divided by positive c has square one, hence equals one. The diagonal pairing fixes the next diagonal. Applying the recurrence once more gives the displayed last-link norm, with zero for an exact terminating order. This proves the order bound, all earlier coefficients, and the short, exact and larger-order alternatives over the reals as well as the rationals. No normalized representation or supplied stem is assumed. The classification consumes this result to exclude all rational competitor orders and to force the positive matrix.", DescribeRole.Theorem),
                Node("tree", "Earn the first departure on the actual tree", "tree_first_departure", tree,
                    "Choose a maximal simple locally saturated rooted stem among the finitely bounded possible lengths. Acyclicity keeps every forward neighbor off that stem. A single forward neighbor would extend it, so maximality excludes boundary size one. The degree bound leaves only zero, two or three; a positive-length stem has at most two forward neighbors. The actual recurrence states are exactly its distinct coordinate vectors, followed by its actual boundary indicator. Thus all earlier norms are one and the next norm is zero, two or three. If the boundary is empty, connectivity exhausts every actual vertex; the path-to-subgraph isomorphism becomes a genuine rooted isomorphism of the whole graph. The theorem supplies, rather than assumes, every stem, Gram and diagonal premise used by the classification.", DescribeRole.Theorem))));
    }
    private static DocumentBlock Node(string id, string title, string name, Formula f, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("tree-endpoint-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? C(s) : App(C(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Conj(params Formula[] a) => a.Length == 1 ? a[0] : And(a[0], Conj(a[1..]));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inv(Formula a) => Pow(a, new Formula.Negate(D(1)));
    private static Formula If(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula Dot(Formula a, Formula b) => Call("dotProduct", a, b);
    private static Formula CV(Formula m, Formula o, Formula a, Formula c, Formula j) => Call("chainVector", m, o, a, c, j);
    private static Formula CN(Formula m, Formula o, Formula a, Formula c, Formula j) => Call("chainNorm", m, o, a, c, j);
    private static Formula GV(Formula p, Formula j) => Call("getVert", p, j);
    private static Formula Len(Formula p) => Call("length", p);
    private static Formula Card(Formula p) => Call("card", p);
    private static Formula Fin(Formula p) => Call("Fin", p);
    private static Formula Mat(Formula v, Formula k) => Call("Matrix", v, v, k);
    private static Formula Type() => C("Type");
    private static Formula Nat() => C("Nat");
    private static Formula Instance(string name, Formula arg, Formula body) => Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Field(Formula b) => All("K", Type(), Instance("Field", V("K"), b));
    private static Formula LinearlyOrdered(Formula b) => Field(Instance("LinearOrder", V("K"), b));
    private static Formula BareGraph(Formula b) => All("V", Type(), All("G", Call("SimpleGraph", V("V")), b));
    private static Formula EqualityGraph(Formula b) => All("V", Type(), Instance("DecidableEq", V("V"), All("G", Call("SimpleGraph", V("V")), Instance("DecidableRel", Call("Adj", V("G")), b))));
    private static Formula EqualityData(Formula b) => Field(All("V", Type(), Instance("DecidableEq", V("V"), b)));
    private static Formula Ordered(Formula b) => Field(Instance("LinearOrder", V("K"), Instance("IsStrictOrderedRing", V("K"), b)));
    private static Formula Carrier(Formula b) => All("V", Type(), Instance("Fintype", V("V"), Instance("DecidableEq", V("V"), b)));
    private static Formula Data(Formula b) => Field(Carrier(b));
    private static Formula GraphBody(Formula b) => Carrier(All("G", Call("SimpleGraph", V("V")), Instance("DecidableRel", Call("Adj", V("G")), b)));
    private static Formula Graph(Formula b) => GraphBody(b);
    private static Formula OrderedGraph(Formula b) => Ordered(GraphBody(b));
    private static Formula StateBody(Formula b) => All("M", Mat(V("V"), V("K")), All("o", V("V"), All("a", V("K"), All("c", V("K"), All("j", Nat(), b)))));
    private static Formula StateData(Formula b) => Data(StateBody(b));
    private static Formula Moments(Formula m, Formula o, Formula j, Formula z, Formula d) => All("k", Nat(), Imp(Le(V("k"), d), Eqn(App(Pow(m, V("k")), o, o), App(Pow(j, V("k")), z, z))));
    private static Formula TwoMatrices(Formula b) => Data(All("W", Type(), Instance("Fintype", V("W"), Instance("DecidableEq", V("W"),
        All("M", Mat(V("V"), V("K")), All("J", Mat(V("W"), V("K")), Imp(Call("IsSymm", V("M")), Imp(Call("IsSymm", V("J")),
            All("o", V("V"), All("z", V("W"), All("a", V("K"), All("c", V("K"), b))))))))))));
}
