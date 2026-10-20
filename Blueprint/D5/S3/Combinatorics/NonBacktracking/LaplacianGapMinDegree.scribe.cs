using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NonBacktracking;

internal sealed class LaplacianGapMinDegreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/mulaszhangzucal2023nonbacktracking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The non-backtracking transition spectrum has gap at most the reciprocal minimum-degree excess.",
        H("Non-backtracking Laplacian gap"),
        Blocks(
            Paragraph(Text("The source defines the non-backtracking graph on oriented edges and the random-walk Laplacian id minus D inverse times A. Its gap is the minimum norm of an eigenvalue of the transition matrix. The following Lean definitions use finite simple graphs on Fin n and the displayed transition weights.")),
            Node("arc", "Oriented edges", "Arc", ArcFormula(), "For a graph G on Fin n, Arc G is the subtype of ordered vertex pairs whose endpoints are adjacent. These are the oriented edges used as states of the transition matrix." , DescribeRole.Definition),
            Node("transition", "Non-backtracking transition", "nbTransition", TransitionFormula(), "The transition from an arc [u,v] to an arc [v,w] has weight 1/(degree(v)-1) exactly when w is different from u; all other entries are zero." , DescribeRole.Definition),
            Node("gap", "Spectral gap", "nbGap", GapFormula(), "The gap is the infimum of the norms of the complex eigenvalues of the complexified transition matrix." , DescribeRole.Definition),
            Node("claim", "Conjecture 5.3", "claim", ClaimFormula(), "The source states verbatim on printed page 16: “If G is not the cycle graph, then ε ≤ 1/(δ−1).” The encoding quantifies over finite simple graphs of positive order with minimum degree at least two, excludes graph isomorphism with the cycle graph, and uses nbGap G for ε." , DescribeRole.Definition),
            Node("eigenpair", "A nonzero eigenvector gives a spectral value", "eigenpair_mem_spectrum", EigenpairFormula(), "For any finite index type with decidable equality, a complex square matrix A, scalar r and nonzero vector x satisfying Matrix.mulVec A x = r • x, the scalar r belongs to spectrum ℂ A. The bound nbGap_le_norm_eigenpair uses this implication for the non-backtracking transition matrix.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The non-backtracking gap bound", "result", ClaimFormula(), "The result proves the quoted Conjecture 5.3. For minimum degree two, the all-ones vector is an eigenvector with eigenvalue one. For minimum degree at least three, the factorization P=RS with symmetric inverse factor T yields a Hermitian pencil T−tR; a dimension count and endpoint sign change give a singular t in [δ−1,Δ), hence a positive real transition eigenvalue at most 1/(δ−1). The cycle exclusion is therefore unnecessary." , DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mulas-zhang-zucal-2023-non-backtracking-gap-min-degree"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role,
        AssessedProvenance? provenance = null, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("nbl-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string value) => F.Id(value);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula CastReal(Formula x) => Parenthesized(Seq(QCall("Nat", "cast", x), Sp, Colon, Sp, Real()));
    private static Formula Complex() => new Formula.NamedConstant(FormulaIdentifier.Create("Complex"));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ge(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(V(name), Sp, Mapsto, Sp, body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ArcFormula() =>
        All("n", Nat(),
            All("G", Call("SimpleGraph", Call("Fin", V("n"))),
                Eqn(Call("Arc", V("G")),
                    Call("Subtype", Call("Prod", Call("Fin", V("n")), Call("Fin", V("n"))),
                        Lambda("p", App(QCall("SimpleGraph", "Adj", V("G")),
                            QCall("Prod", "fst", V("p")), QCall("Prod", "snd", V("p"))))))));
    private static Formula TransitionFormula()
    {
        Formula a = V("a");
        Formula b = V("b");
        Formula g = V("G");
        Formula va = QCall("Subtype", "val", a);
        Formula vb = QCall("Subtype", "val", b);
        Formula tailA = QCall("Prod", "snd", va);
        Formula tailB = QCall("Prod", "fst", vb);
        Formula headB = QCall("Prod", "snd", vb);
        Formula headA = QCall("Prod", "fst", va);
        Formula condition = And(Eqn(tailA, tailB), new Formula.Not(Eqn(headB, headA)));
        Formula degree = QCall("SimpleGraph", "degree", g, tailA);
        Formula weight = new Formula.Fraction(D(1), new Formula.Binary(CastReal(degree), FormulaBinaryOperator.Subtract, D(1)));
        Formula entry = Call("ite", condition, weight, D(0));
        Formula body = Eqn(Call("nbTransition", g, a, b), entry);
        return All("n", Nat(),
            All("G", Call("SimpleGraph", Call("Fin", V("n"))),
                Seq(Instance("DecidableRel", QCall("SimpleGraph", "Adj", V("G"))), Sp,
                    All("a", Call("Arc", V("G")),
                    All("b", Call("Arc", V("G")), body)))));
    }
    private static Formula SetWhere(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula EigenpairFormula()
    {
        Formula index = V("iota"), a = V("A"), r = V("r"), x = V("x");
        Formula vectorType = Seq(index, Sp, To, Sp, Complex());
        Formula eigenpair = Eqn(QCall("Matrix", "mulVec", a, x), QCall("HSMul", "hSMul", r, x));
        return All("iota", Seq(Operatorname, Grp(V("Type")), Star),
            Seq(Instance("Fintype", index), Sp, Instance("DecidableEq", index), Sp,
                All("A", Call("Matrix", index, index, Complex()),
                    All("r", Complex(), All("x", vectorType,
                        Imp(new Formula.Not(Eqn(x, D(0))),
                            Imp(eigenpair, Member(r, Call("spectrum", Complex(), a)))))))));
    }
    private static Formula GapFormula()
    {
        Formula n = V("n"), g = V("G"), r = V("r"), mu = V("mu");
        Formula transition = Call("nbTransition", g);
        Formula complexified = QCall("Matrix", "map", transition,
            QCall("Algebra", "algebraMap", new Formula.NamedConstant(FormulaIdentifier.Create("Real")),
                new Formula.NamedConstant(FormulaIdentifier.Create("Complex"))));
        Formula spectrum = Call("spectrum", Complex(), complexified);
        Formula values = SetWhere("r", new Formula.NamedConstant(FormulaIdentifier.Create("Real")),
            Exists("mu", Complex(),
                And(Member(mu, spectrum), Eqn(r, new Formula.Norm(mu)))));
        return All("n", Nat(),
            All("G", Call("SimpleGraph", Call("Fin", n)),
                Seq(Instance("DecidableRel", QCall("SimpleGraph", "Adj", g)), Sp,
                    Eqn(Call("nbGap", g), Call("sInf", values)))));
    }
    private static Formula ClaimFormula()
    {
        Formula n = V("n");
        Formula G = V("G");
        Formula degree = QCall("SimpleGraph", "minDegree", G);
        Formula hcycle = new Formula.Not(Call("Nonempty",
            QCall("SimpleGraph", "Iso", G, QCall("SimpleGraph", "cycleGraph", n))));
        Formula conclusion = Le(Call("nbGap", G),
            new Formula.Fraction(D(1), new Formula.Binary(CastReal(degree), FormulaBinaryOperator.Subtract, D(1))));
        return All("n", Nat(),
            All("G", Call("SimpleGraph", Call("Fin", n)),
                Seq(Instance("DecidableRel", QCall("SimpleGraph", "Adj", G)), Sp,
                    Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
                        Imp(Ge(degree, D(2)), Imp(hcycle, conclusion))))));
    }
}
