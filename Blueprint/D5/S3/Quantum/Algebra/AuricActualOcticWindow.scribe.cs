using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricActualOcticWindowDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(Seq(Open, x, Close), op, Seq(Open, y, Close));
    private static Formula And(params Formula[] xs) =>
        xs.Reverse().Aggregate((x, y) => Logic(y, FormulaLogicOperator.And, x));
    private static Formula Imp(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Instance(string name, params Formula[] xs) => Seq(OpenBracket, Call(name, xs), CloseBracket, Sp);

    private static Formula Statement()
    {
        var f = V("F"); var d = V("D"); var k = V("K"); var w = V("W"); var a = V("a");
        var e = V("e"); var u = V("U"); var n = V("n"); var m = V("N"); var s = V("S");
        var g = V("g"); var sigma = V("sigma"); var tau = V("tau");
        var omega = Call("AlgHom", f, d, k);
        var coordinates = Call("Map", omega, k);
        var complement = Call("compl", s);
        Formula Rho(Formula t) => Call("finrank", k, Call("map", u, Call("coordinateProject", t)));
        Formula Block(Formula x, Formula y) => Call("rank", Call("block", m, x, y));
        var conclusions = And(
            Equal(Call("compose", n, n), D(0)), Equal(Call("range", n), u), Equal(Call("ker", n), u),
            Equal(Mul(m, m), D(0)), Equal(Call("rank", m), D(4)),
            All("g", Call("AlgEquiv", f, k, k), All("sigma tau", omega,
                Equal(Call("entry", m, Call("compose", g, sigma), Call("compose", g, tau)),
                    Call("apply", g, Call("entry", m, sigma, tau))))),
            All("S", Call("Finset", omega), Imp(And(Call("Nonempty", s), Call("Nonempty", complement)),
                Leq(Add(Call("card", s), D(1)), Mul(D(2), Rho(s))))),
            All("S", Call("Finset", omega), Imp(And(Leq(D(2), Call("card", s)), Leq(Call("card", s), D(6))),
                Logic(Leq(D(2), Block(s, complement)), FormulaLogicOperator.Or, Leq(D(2), Block(complement, s))))));
        var definitions = All("U", Call("Submodule", k, coordinates),
            Imp(Equal(u, Call("map", Call("baseChange", k, w), Call("linear", e))),
            All("n", Call("LinearMap", k, coordinates, coordinates),
            Imp(Equal(n, Call("compose", Call("linear", e), Call("baseChange", k, Call("actualOperator", w, a)),
                    Call("linear", Call("inverse", e)))),
            All("N", Call("Matrix", omega, omega, k), Imp(Equal(m, Call("toMatrix", n)), conclusions))))));
        var splitting = Some("e", Call("AlgEquiv", k, Call("Tensor", f, k, d), coordinates), And(
            All("c", k, All("z", d, All("sigma", omega,
                Equal(Call("apply", e, Call("tensor", V("c"), V("z")), sigma),
                    Mul(V("c"), Call("apply", sigma, V("z"))))))), definitions));
        var premises = And(Equal(Call("finrank", f, d), D(8)), Equal(Call("finrank", f, w), D(4)),
            Equal(Call("Idealizer", f, d, w), Call("range", Call("algebraMap", f, d))),
            Seq(Neg, Sp, Rel(a, FormulaRelationOperator.MemberOf, Call("quotientSet", w))));
        return All("F D K", V("Type"), Seq(
            Instance("Field", f), Instance("Field", d), Instance("Field", k),
            Instance("Algebra", f, d), Instance("Algebra", f, k), Instance("Algebra", d, k),
            Instance("IsScalarTower", f, d, k), Instance("FiniteDimensional", f, d),
            Instance("CharZero", f), Instance("FiniteDimensional", f, k), Instance("Normal", f, k),
            All("W", Call("Submodule", f, d), All("a", d,
                Imp(premises, And(Call("Bijective", Call("obstruction", w, a)), splitting))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cut-free theorem for an arbitrary actual octic window.",
        H("Actual octic windows with scalar multiplication idealizer"),
        Blocks(
            Paragraph(Text(
                "F has characteristic zero, D/F is an arbitrary extension of degree eight, and W is an "
                + "arbitrary four dimensional F subspace of D. Its multiplication idealizer is exactly F. "
                + "Q(W) consists of u/v with u and v in W and v nonzero; since W is nonzero this includes zero. "
                + "K/F is any finite normal extension containing this same D, including its normal closure. "
                + "Omega is the literal type of all F algebra embeddings D to K.")),
            Paragraph(Text(
                "In the formula, Map(Omega,K) is the coordinate function space; Tensor(F,K,D) is K tensor over F D. "
                + "Idealizer(F,D,W) is the set of c in D with c W contained in W. coordinateProject(S) retains "
                + "the coordinates in S and is zero elsewhere. block(N,S,T) is the literal submatrix with row "
                + "and column subtypes S and T. The universally quantified U, n and N are constrained to their "
                + "displayed definitions; this expresses the original let bindings without adding a hypothesis.")),
            Describe.Lean(
                DescribeId.Create("actual-general43-2-cut-free"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/AuricActualOcticWindow.general43_2_cut_free"),
                H("The original actual cut-free clause"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a outside Q(W), A(a) is multiplication by a on W followed by D/W. "
                        + "A nonzero kernel vector would exhibit a as a quotient of two elements of W, "
                        + "so A(a) is injective; both spaces have dimension four, hence it is invertible. "
                        + "The original operator is n = inclusion composed with A(a) inverse and the quotient map. "
                        + "The canonical K algebra splitting sends c tensor d to the function sigma maps to "
                        + "c times sigma(d). Under this splitting, the scalar extension of n has square zero "
                        + "and has image and kernel exactly the image of K tensor W. Its actual matrix N has "
                        + "square zero, rank four, and the covariance N(g sigma,g tau) = g(N(sigma,tau)).")),
                    Paragraph(Text(
                        "Write rho(S) for the dimension of the projection of this actual split window onto S. "
                        + "Coefficient extraction along an F basis of K shows that a tensor preserving the "
                        + "window has every coefficient in the original multiplication idealizer. Consequently "
                        + "every diagonal stabilizer of the split window is scalar. Equality in the complementary "
                        + "projection dimension bound would give a nonconstant indicator stabilizer, so the row "
                        + "rank is connected. The actual Galois action is transitive on Omega and preserves rho. "
                        + "Applying the existing fractional submodular cover theorem to the orbit of S gives "
                        + "2 rho(S) at least the cardinality of S. For the nonnegative submodular defect "
                        + "2 rho(S) minus the cardinality of S, a minimal nonempty zero set has translates "
                        + "which cannot cross a zero set. Their union proves that the complement of a zero set "
                        + "is zero. Connectivity excludes this equality for every nonempty proper S. Thus "
                        + "2 rho(S) is at least the cardinality of S plus one, derived from the same actual W.")),
                    Paragraph(Text(
                        "Rank-nullity applied twice to n restricted to the complementary coordinate space gives "
                        + "2 rho(S) at most the cardinality of S plus rank N[S,S complement]. If both crossing "
                        + "ranks were at most one for a cut of size two through six, strict rank forces a triple C "
                        + "with rho(C)=2 and rho(C complement)=3. Two conjugate triples cannot meet in two points, "
                        + "by submodularity on the triples and strict rank on their intersection and union. They "
                        + "cannot meet in one point, by applying the same argument to one triple and the complement "
                        + "of the other. Distinct conjugate triples are therefore disjoint. Transitivity would "
                        + "partition eight labels into triples, a contradiction. Hence at least one actual crossing "
                        + "block has rank at least two. This is the cut-free clause of the existing source argument; "
                        + "the full classification and the separate fixed-N irreducibility bridge remain open. "
                        + "The rank machinery is supplied by AuricOcticRanks and is consumed here on the actual "
                        + "window. There is no general-position, uniformity, connectivity or certificate premise, "
                        + "and no normalization requiring one to lie in W. No mathematical novelty is claimed.")),
                    Paragraph(Text(
                        "Four-slot source registration remains unfinished; its concrete reconstruction and "
                        + "variation obligations are recorded in https://github.com/the-omega-institute/trureturing/issues/29718. "
                        + "No declared_validated registration status is asserted."))),
                DescribeRole.Theorem))));
}
