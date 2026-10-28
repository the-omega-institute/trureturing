using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class RatherBookRootRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Geometry/rather2026bookroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal arXiv v1/v2 all-positive-order book domination-root conjecture fails at the four-cycle.",
        H("Real-root configurations of book domination polynomials"),
        Blocks(
            Paragraph(Text("The source is Conjecture 5.4 in arXiv v1/v2, with the shared-edge four-cycle books of Section 2 for every natural n at least one. Root locations lie on the Euclidean real line, and multiplicities count repeated points. The graph and ordinary dominating-set count are retained in full.")),
            Node("page-forward", "Directed page edges", "pageForward", DescribeRole.Definition,
                Vertices(Eq(Call("pageForward", X("n"), X("u"), X("v")), P(PageBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Section 2, printed page 3 and Figure 1(b): n copies of C4 have one common edge and otherwise disjoint vertices. The vertices are Fin (2*n+2); the displayed Fin.val maps explicitly take each vertex or page index to Nat. The shared edge is 0--1, and page i continues 1--(2*i.val+2)--(2*i.val+3)--0. These are all the forward edges."),
            Node("page-decision", "Deciding a directed page edge", "instDecidablePageForward", DescribeRole.Definition,
                Vertices(Typed(Call("instDecidablePageForward", X("n"), X("u"), X("v")),
                    Call("Decidable", P(Call("pageForward", X("n"), X("u"), X("v")))))),
                AssessedProvenance.FromRepo(Source),
                "The instance unfolds pageForward and uses infer_instance: natural equalities, conjunctions and disjunctions are decidable, and the existential page index ranges over Fin n. This supplies the decisions used by the adjacency instance and the finite comparison with cycleGraph 4."),
            Node("book", "The undirected loopless book", "bookGraph", DescribeRole.Definition,
                All("n", Nat(), Eq(
                    App(Q("SimpleGraph", "Adj"), Typed(Call("bookGraph", X("n")), Call("SimpleGraph", VertexType()))),
                    P(Seq(LambdaLower, Sp, Typed(X("u"), VertexType()), Sp, Mapsto, Sp,
                        LambdaLower, Sp, Typed(X("v"), VertexType()), Sp, Mapsto, Sp,
                        Or(Call("pageForward", X("n"), X("u"), X("v")),
                            Call("pageForward", X("n"), X("v"), X("u"))))))),
                AssessedProvenance.FromLiterature(Source),
                "Section 2 defines the simple undirected shared-edge book. The defining Adj field is exactly the displayed symmetrization. The symm field is the proof fun u v h => h.symm, packaged as Std.Symm. The loopless field has type Std.Irrefl for this adjacency. For loopless, both disjuncts reduce to pageForward n v v: the shared-edge equalities force 0=1; each page alternative forces either 1=2*i.val+2, consecutive naturals equal, or 2*i.val+3=0. The source proves all cases with omega and combines the two exclusions by h.elim. Thus the structure has no loops and no additional edges."),
            Node("adjacency-decision", "Deciding book adjacency", "instDecidableRelFinHAddNatHMulOfNatAdjBookGraph", DescribeRole.Definition,
                All("n", Nat(), All("u", VertexType(), All("v", VertexType(), Eq(
                    App(Typed(Call("instDecidableRelFinHAddNatHMulOfNatAdjBookGraph", X("n")),
                        Call("DecidableRel", App(Q("SimpleGraph", "Adj"), Call("bookGraph", X("n"))))), X("u"), X("v")),
                    Call("inferInstanceAs", P(Call("Decidable", P(Or(
                        Call("pageForward", X("n"), X("u"), X("v")),
                        Call("pageForward", X("n"), X("v"), X("u"))))))))))),
                AssessedProvenance.FromRepo(Source),
                "The defining method is fun u v => inferInstanceAs (Decidable (pageForward n u v or pageForward n v u)). The two previously defined directed-edge decisions supply the decidable disjunction. This is a decision procedure for precisely the displayed adjacency relation."),
            Node("polynomial", "Ordinary domination polynomial", "dominationPolynomial", DescribeRole.Definition,
                All("V", X("Type"), All("instF", Call("Fintype", X("V")),
                    All("instD", Call("DecidableEq", X("V")), All("G", Call("SimpleGraph", X("V")),
                        Eq(Call("dominationPolynomial", X("V"), X("instF"), X("instD"), X("G")),
                            Seq(F.Sum, Underscore, Grp(Seq(X("S"), Sp, InMacro, Sp,
                                App(Q("DominatingSetAverage", "domSets"), X("V"), X("instF"), X("G")))), Sp,
                                new Formula.Power(P(Typed(Q("Polynomial", "X"), PolynomialType())),
                                    App(Q("Finset", "card"), X("S"))))))))),
                AssessedProvenance.FromLiterature(Source),
                "The source definition of D(G,x) counts ordinary dominating subsets once, by their cardinality. Here instF and instD name the Fintype and DecidableEq arguments; applications display these normally implicit arguments explicitly in their Lean order. The sum uses the existing DominatingSetAverage.domSets, whose membership theorem is mem_domSets and whose predicate is the existing SimpleGraph.IsDominating: every vertex belongs to S or has a neighbor in S. Coefficients are real and Polynomial.X has type Polynomial Real. No count is assumed."),
            Node("four-roots", "Exact multiplicities and exhaustive roots", "FourRealRoots", DescribeRole.Definition,
                All("p", PolynomialType(), All("a", Real(), All("b", Real(),
                    Eq(Call("FourRealRoots", X("p"), X("a"), X("b")), P(FourRootsBody()))))),
                AssessedProvenance.FromLiterature(Source),
                "Conjecture 5.4, printed page 12: exactly four real roots counting multiplicity means a double zero and two distinct simple nonzero roots. Polynomial.IsRoot and Polynomial.rootMultiplicity are the actual polynomial predicates. The final equivalence ranges over every real r and excludes any further real root."),
            Node("claim", "The complete arXiv conjecture", "claim", DescribeRole.Definition,
                Eq(Typed(X("claim"), X("Prop")), P(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                "Conjecture 5.4 retains every n at least one and both parity implications. For even n the simple roots lie below -2 and between -1/2 and zero. For odd n both lie between -1/2 and zero. FourRealRoots includes all exact multiplicities and the root equivalence for every real number. The rational endpoint is negative one divided by two in Real."),
            Node("result", "The order-one book contradicts the universal conjecture", "result", DescribeRole.Theorem,
                new Formula.Not(P(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "The order-one book equals SimpleGraph.cycleGraph 4. Exactly its six two-element subsets, four three-element subsets and full vertex set dominate; the empty set and four singletons do not. The finite comparison and enumeration are checked by kernel decision, using mem_domSets. Summing the eleven actual subsets gives 6*X^2+4*X^3+X^4. Evaluation at a factors as a^2*((a+2)^2+2), strictly positive for every nonzero a. Instantiating the odd implication at n=1 supplies a nonzero root a, a contradiction. The private book_one_eq_cycle and cycle_domSets establish book_one_polynomial, which supplies this evaluation. The C4 count, book polynomial and positive-cofactor argument are established ingredients; no new general root theorem is asserted.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rather-2026-book-domination-root-conjecture"),
                    ResolutionKind.Refuted)),
            Paragraph(Text("The author bibliography lists the paper as Filomat (2026), to appear. The journal text and any corrections remain unread, so agreement with a journal statement is not asserted. The relevant six-page 2013 article also remains unread; its located arXiv document contains only an abstract. The argument refutes the literal arXiv v1/v2 universal statement at n=1. The separately amended n at least two statement remains unsettled. No global literature priority or exhaustive ownership conclusion follows."))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, DescribeRole role,
        Formula formula, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula PolynomialType() => Call("Polynomial", Real());
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Q(string owner, string field) => Seq(Operatorname, Grp(Seq(X(owner), Dot, X(field))));
    private static Formula P(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => P(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Or, P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Val(string name) => App(Q("Fin", "val"), X(name));
    private static Formula VertexType() => Call("Fin", P(Add(Mul(D(2), X("n")), D(2))));
    private static Formula Vertices(Formula body) => All("n", Nat(), All("u", VertexType(), All("v", VertexType(), body)));
    private static Formula PageBody() => Or(And(Eq(Val("u"), D(0)), Eq(Val("v"), D(1))),
        Some("i", Call("Fin", X("n")), Or(And(Eq(Val("u"), D(1)), Eq(Val("v"), Add(Mul(D(2), Val("i")), D(2)))),
            Or(And(Eq(Val("u"), Add(Mul(D(2), Val("i")), D(2))), Eq(Val("v"), Add(Mul(D(2), Val("i")), D(3)))),
                And(Eq(Val("u"), Add(Mul(D(2), Val("i")), D(3))), Eq(Val("v"), D(0)))))));
    private static Formula Root(Formula r) => App(Q("Polynomial", "IsRoot"), X("p"), r);
    private static Formula Multiplicity(Formula r) => App(Q("Polynomial", "rootMultiplicity"), r, X("p"));
    private static Formula FourRootsBody() => And(Ne(X("a"), D(0)), And(Ne(X("b"), D(0)), And(Ne(X("a"), X("b")),
        And(Root(D(0)), And(Root(X("a")), And(Root(X("b")), And(Eq(Multiplicity(D(0)), D(2)),
        And(Eq(Multiplicity(X("a")), D(1)), And(Eq(Multiplicity(X("b")), D(1)),
            All("r", Real(), new Formula.Logic(Root(X("r")), FormulaLogicOperator.Iff,
                P(Or(Eq(X("r"), D(0)), Or(Eq(X("r"), X("a")), Eq(X("r"), X("b"))))))))))))))));
    private static Formula HalfNegative() => new Formula.Negate(new Formula.Fraction(Typed(D(1), Real()), Typed(D(2), Real())));
    private static Formula FourAtBook() => Call("FourRealRoots", Call("dominationPolynomial", Call("bookGraph", X("n"))), X("a"), X("b"));
    private static Formula ClaimBody() => All("n", Nat(), Imp(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, X("n")),
        And(Imp(Call("Even", X("n")), Some("a", Real(), Some("b", Real(),
                And(Lt(X("a"), new Formula.Negate(D(2))), And(Lt(HalfNegative(), X("b")), And(Lt(X("b"), D(0)), FourAtBook())))))),
            Imp(Call("Odd", X("n")), Some("a", Real(), Some("b", Real(),
                And(Lt(HalfNegative(), X("a")), And(Lt(X("a"), D(0)),
                    And(Lt(HalfNegative(), X("b")), And(Lt(X("b"), D(0)), FourAtBook()))))))))));
}
