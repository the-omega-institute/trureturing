using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PathMiddleEdgeMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kirkland2019rationalweightspst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be the Hamiltonian of a weighted path on the 2k + 2 vertices 0, ..., 2k + 1, with positive edge weights and real potentials, whose propagator exp(i pi H) has the entry 1 at the last and first vertices. Then the eigenvalues of H are distinct integers that are even on a class A of k + 1 indices and odd on the other k + 1, the eigenvectors of the odd class have opposite entries at the two middle vertices a = k and b = k + 1, and the eigenvector of index j in A satisfies |W(a, j) + W(b, j)|^2 = prod_{l not in A} (z j - z l) / (rho prod_{l in A, l != j} (z j - z l)), where rho is the weight of the middle edge. With S p the sum of the four entries of H^p at a and b, the number rho S p is the integer coefficient of X^k in the remainder of X^p P_B modulo P_A, for the nodal polynomials P_A and P_B of the two classes, and S 0 S 2 - (S 1)^2 = 4 r'^2 for the weight r' of the edge following the middle edge.",
        H("Middle-edge spectral weights, integer moments and Gram identity of even paths with end transfer at time pi"),
        Blocks(
            Node("pairmoment", "The moment of a matrix at the sum of two basis vectors", PairMomentFormula(),
                "For a square complex matrix H indexed by a finite type V and two indices a and b, the moment of order p at the vector f = e_a + e_b is f^T H^p f, the sum of the four entries of H^p at the indices a and b. For a real symmetric matrix H it is the moment of order p of the spectral measure of H at f. It is used for the path Hamiltonian at the two ends of the middle edge of a path with an even number of vertices.",
                "pairMoment", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("nodalmoment", "The nodal moments of one finite set of integer nodes against another", NodalMomentFormula(),
                "For integers z indexed by a type iota and finite sets A and B of indices, let P_A and P_B be the monic polynomials with the roots z l, l in A, and z l, l in B. The nodal moment of order p and degree k is the coefficient of X^k in the remainder of X^p P_B modulo P_A, an integer. In the formal statement modByMonic is the remainder of the division by a monic polynomial, coeff extracts a coefficient, and C embeds the integers into the integer polynomials. When A has k + 1 elements and the nodes of A are distinct, the Lagrange coefficient formula identifies it with the divided difference sum over j in A of z_j^p P_B(z j) / prod_{l in A, l != j} (z j - z l).",
                "nodalMoment", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("weights", "Spectral weights at the middle edge", WeightsFormula(),
                "Let W be the unitary matrix of orthonormal eigenvectors of H and lambda k its eigenvalues. The reversal sign classes of the spectrum of a path with transfer of phase one give distinct integers z with lambda k = z k, even on a class A and odd off A, with W(rev x, k) = W(x, k) for k in A and W(rev x, k) = -W(x, k) otherwise, with #A - #A^c equal to the number of vertices fixed by the reversal, and with |W(0, j)|^2 prod_{l != j} (z j - z l) equal to the product of all the weights for j in A. The reversal rev x = 2k + 1 - x has no fixed vertex, so #A = #A^c = k + 1; it exchanges the middle vertices a = k and b = k + 1, so W(a, j) + W(b, j) = 0 for j outside A. By the mirror symmetry of the weights, the product of all the weights is rho Q^2, where rho = r(k) is the weight of the middle edge e and Q = r(0) r(1) ... r(k - 1). The entries of H^p at a and the first vertex vanish for p < k and equal Q for p = k, and the entries at b and the first vertex vanish for p <= k; only the indices of A contribute to the sum of the two, so evaluating these moment relations on nodal polynomials gives (W(a, j) + W(b, j)) conj(W(0, j)) prod_{l in A, l != j} (z j - z l) = Q for j in A. Dividing the squared modulus of this relation by the relation at the first vertex gives the stated formula. In the formal statement eigenvalues and eigenvectorUnitary are the eigenvalues and the eigenvector matrix attached to the Hermitian matrix H, hamiltonianPropagator H s = exp(-i s H) is the repository propagator taken at s = -pi, last(2k + 1) is the vertex 2k + 1, and a, b, e are a vertex of value k, a vertex of value k + 1 and an edge of value k. The source records as known that the eigenvectors of a mirror-symmetric Hamiltonian are symmetric or antisymmetric, citing Cantoni and Butler, and that after a common shift the eigenvalues of a path with perfect state transfer at time pi between its end vertices are integers that alternate between even and odd. The count #A = k + 1 and the formula for the squared modulus at the middle edge are derived here.",
                "middle_edge_weights", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("moments", "Integer moments at the middle edge", MomentsFormula(),
                "By the spectral theorem the moment S p of H^p at e_a + e_b is the sum over the eigenvector indices j of lambda_j^p |W(a, j) + W(b, j)|^2. The indices outside A do not contribute, and by the spectral weights at the middle edge rho S p is the sum over j in A of z_j^p P_B(z j) / prod_{l in A, l != j} (z j - z l), where P_A and P_B are the monic integer polynomials whose roots are the eigenvalues of the even class A and of the odd class. By the Lagrange coefficient formula over the k + 1 nodes of A, this sum is the coefficient of X^k in the remainder of X^p P_B modulo P_A, the nodal moment of order p of A against its complement. In the formal statement the equality holds between complex numbers, the weight rho = r e and the integer nodal moment being cast. For p = 0 the remainder is P_B - P_A and S 0 = 2, so 2 rho is the sum of the eigenvalues of the even class minus the sum of those of the odd class. The source's corollary on middle weights gives the middle weight of a mirror-symmetric path with an even number of vertices as S_1 / 2, where S_1 is the alternating sum of the ordered eigenvalues; the integrality of rho S p for every p is derived here.",
                "middle_edge_moments", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("gram", "Gram identity of the middle-edge moments", GramFormula(),
                "Let H be the path Hamiltonian on the vertices 0, ..., 2k + 1, invariant under the reversal rev x = 2k + 1 - x, and let f be the edge following the middle edge, so that k >= 1. Write S p for the moment of H^p at e_a + e_b, with a = k and b = k + 1 the ends of the middle edge, and v(x) = H(x, a) + H(x, b) for the column of H at e_a + e_b. Since H is real symmetric, S 0 = 2, S 1 = v(a) + v(b) and S 2 = sum_x v(x)^2. The column v is invariant under the reversal, vanishes outside the four vertices k - 1, k, k + 1, k + 2, and its entry at the vertex k + 2 is the weight r(k + 1) of the edge f. Hence S 1 = 2 v(a), S 2 = 2 v(a)^2 + 2 r(k + 1)^2 and S 0 S 2 - (S 1)^2 = 4 r(k + 1)^2. In the formal statement the weight r f is cast to a complex number. The identity is the expression of the second Hankel determinant of the moments of a Jacobi matrix by its first off-diagonal entry, for the block acting on the reversal-invariant vectors, whose first off-diagonal entry is the weight next to the middle edge; it is derived here directly for the path Hamiltonian. For n = 4 the source computes the weight next to the middle edge from the eigenvalues and shows that it is irrational.",
                "middle_edge_gram", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("midedge-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Entry(Formula m, Formula x, Formula y) => App(m, x, y);
    private static Formula PathH(Formula r, Formula q) => Call("pathHamiltonian", r, q);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NotIn(Formula a, Formula s) =>
        new Formula.Not(Parenthesized(Seq(a, Sp, InMacro, Sp, s)));
    private static Formula BigProd(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(index, Sp, InMacro, Sp, set)), Sp, body);

    private static Formula EdgeCount(Formula k) => Add(Mul(D(2), k), D(1));
    private static Formula Edges(Formula k) => FinOf(EdgeCount(k));
    private static Formula Vertices(Formula k) => FinOf(Add(EdgeCount(k), D(1)));
    private static Formula Positive(Formula k, Formula r) =>
        All("t", Edges(k), Less(D(0), App(r, F.Id("t"))));
    private static Formula PhaseOne(Formula k, Formula h) =>
        Equal(Call("hamiltonianPropagator", h, Neg(Pi), Call("last", EdgeCount(k)), D(0)), D(1));
    private static Formula OverPaths(Formula body)
    {
        Formula k = F.Id("k");
        return Disp(All("k", Naturals(), All("r", Arrow(Edges(k), Reals()),
            All("q", Arrow(Vertices(k), Reals()), body))));
    }

    private static Formula MiddleEdge(Formula k, Formula conclusion)
    {
        Formula a = F.Id("a"), b = F.Id("b"), e = F.Id("e");
        return All("a", Vertices(k), All("b", Vertices(k),
            Implies(Equal(Cast(a, Naturals()), k), Implies(Equal(Cast(b, Naturals()), Add(k, D(1))),
                All("e", Edges(k), Implies(Equal(Cast(e, Naturals()), k), conclusion))))));
    }

    private static Formula PairMomentFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), a = F.Id("a"), b = F.Id("b"), p = F.Id("p");
        Formula power = new Formula.Power(h, p);
        Formula sum = Add(Add(Add(Entry(power, a, a), Entry(power, a, b)), Entry(power, b, a)),
            Entry(power, b, b));
        Formula body = All("H", Call("Matrix", v, v, Complexes()), All("a", v, All("b", v,
            All("p", Naturals(), Equal(Call("pairMoment", h, a, b, p), sum)))));
        return Disp(All("V", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp, body)));
    }

    private static Formula NodalMomentFormula()
    {
        Formula iota = F.Id("iota"), z = F.Id("z"), sa = F.Id("A"), sb = F.Id("B"), k = F.Id("k"),
            p = F.Id("p"), l = F.Id("l"), x = F.Id("X");
        Formula factor = Parenthesized(Sub(x, Call("C", App(z, l))));
        Formula dividend = Mul(new Formula.Power(x, p), BigProd(l, sb, factor));
        Formula remainder = Call("modByMonic", dividend, BigProd(l, sa, factor));
        return Disp(All("iota", F.Id("Type"), All("z", Arrow(iota, Integers()),
            All("A", Call("Finset", iota), All("B", Call("Finset", iota),
                All("k", Naturals(), All("p", Naturals(),
                    Equal(Call("nodalMoment", z, sa, sb, k, p), Call("coeff", remainder, k)))))))));
    }

    private static Formula WeightsFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), q = F.Id("q"), a = F.Id("a"), b = F.Id("b"),
            e = F.Id("e"), z = F.Id("z"), s = F.Id("A"), j = F.Id("j"), l = F.Id("l");
        Formula h = PathH(r, q);
        Formula w = Call("eigenvectorUnitary", h);
        Formula pair = Add(Entry(w, a, j), Entry(w, b, j));
        Formula difference = Cast(Cast(Sub(App(z, j), App(z, l)), Integers()), Reals());
        Formula ratio = new Formula.Fraction(
            BigProd(l, Call("compl", s), difference),
            Mul(App(r, e), BigProd(l, Call("erase", s, j), difference)));
        Formula weight = All("j", s, Equal(Call("normSq", pair), ratio));
        Formula vanish = All("j", Vertices(k), Implies(NotIn(j, s), Equal(pair, D(0))));
        Formula spectrum = All("j", Vertices(k),
            Equal(Call("eigenvalues", h, j), Cast(App(z, j), Reals())));
        Formula oddOff = All("j", Vertices(k), Implies(NotIn(j, s), Call("Odd", App(z, j))));
        Formula evenOn = All("j", s, Call("Even", App(z, j)));
        Formula classes = Some("z", Arrow(Vertices(k), Integers()), Some("A", Call("Finset", Vertices(k)),
            And(Call("Injective", z), And(Equal(Call("card", s), Add(k, D(1))),
                And(Parenthesized(evenOn), And(Parenthesized(oddOff), And(Parenthesized(spectrum),
                    And(Parenthesized(vanish), Parenthesized(weight)))))))));
        return OverPaths(Implies(Call("IsHermitian", h), Implies(Parenthesized(Positive(k, r)),
            Implies(PhaseOne(k, h), MiddleEdge(k, classes)))));
    }

    private static Formula MomentsFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), q = F.Id("q"), a = F.Id("a"), b = F.Id("b"),
            e = F.Id("e"), z = F.Id("z"), s = F.Id("A"), j = F.Id("j"), p = F.Id("p");
        Formula h = PathH(r, q);
        Formula complement = Call("compl", s);
        Formula integer = All("p", Naturals(), Equal(
            Mul(Cast(App(r, e), Complexes()), Call("pairMoment", h, a, b, p)),
            Cast(Cast(Call("nodalMoment", z, s, complement, k, p), Integers()), Complexes())));
        Formula oddOn = All("j", complement, Call("Odd", App(z, j)));
        Formula evenOn = All("j", s, Call("Even", App(z, j)));
        Formula classes = Some("z", Arrow(Vertices(k), Integers()), Some("A", Call("Finset", Vertices(k)),
            And(Equal(Call("card", s), Add(k, D(1))), And(Equal(Call("card", complement), Add(k, D(1))),
                And(Parenthesized(evenOn), And(Parenthesized(oddOn), Parenthesized(integer)))))));
        return OverPaths(Implies(Parenthesized(Positive(k, r)),
            Implies(PhaseOne(k, h), MiddleEdge(k, classes))));
    }

    private static Formula GramFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), q = F.Id("q"), x = F.Id("x"), y = F.Id("y"),
            a = F.Id("a"), b = F.Id("b"), f = F.Id("f");
        Formula h = PathH(r, q);
        Formula invariant = All("x", Vertices(k), All("y", Vertices(k),
            Equal(Entry(h, Call("rev", x), Call("rev", y)), Entry(h, x, y))));
        Formula determinant = Sub(
            Mul(Call("pairMoment", h, a, b, D(0)), Call("pairMoment", h, a, b, D(2))),
            new Formula.Power(Call("pairMoment", h, a, b, D(1)), D(2)));
        Formula value = Mul(D(4), new Formula.Power(Cast(App(r, f), Complexes()), D(2)));
        Formula body = Implies(Parenthesized(invariant), All("a", Vertices(k), All("b", Vertices(k),
            Implies(Equal(Cast(a, Naturals()), k), Implies(Equal(Cast(b, Naturals()), Add(k, D(1))),
                All("f", Edges(k), Implies(Equal(Cast(f, Naturals()), Add(k, D(1))),
                    Equal(determinant, value))))))));
        return OverPaths(body);
    }
}
