using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class LinWangCaiBroomSpectralRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/linwangcai2023laplacianratio");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At order nineteen the broom with seven star leaves has larger Laplacian ratio than the broom with eight.",
        H("An order-19 counterexample to the broom spectral-ratio conjecture"),
        Blocks(
            Node("lap-eig", "lapEig", "Ordered Laplacian eigenvalues", EigenvalueFormula(),
                "Page 2 states: “The Laplacian matrix of G with n vertices, denoted by L(G), is given by L(G) = D(G) − A(G), where A(G) is the adjacency matrix and D(G) is the diagonal matrix of its vertex degrees. And the largest and second smallest Laplacian eigenvalues of G are called the Laplacian spectral radius and algebraic connectivity of G, denoted by µ1(G) and µn−1(G).” The index i is zero based, so lapEig G i represents µᵢ₊₁(G). In the formula h is any Hermitian proof and e is any proof identifying the two finite index sizes; proof irrelevance makes these choices immaterial. The eigenvalues are in nonincreasing order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spectral-ratio", "spectralRatio", "Laplacian spectral ratio", RatioFormula(),
                "Page 2 states: “The Laplacian spectral ratio of a connected graph G with n vertices is defined as R_L(G) = µ1(G)/µn−1(G).” The numerator has index zero and the denominator index n - 2. The value below order two is zero. Indices in the two-or-more branch carry the inequalities required by Fin; subtraction is natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("broom", "broom", "Broom tree", BroomFormula(),
                "Page 13 states: “A broom tree B_n^t, shown in Figure 2, is a tree obtained from the path P_{n−t−1} and the star K_{1,t} by joining one pendant vertex of P_{n−t−1} and the center of K_{1,t} by an edge.” Figure 2 labels the center v0, the star leaves v1 through vt, and the path v_{t+1} through v_{n−1}. SimpleGraph.fromRel symmetrizes the displayed relation and removes loops. The coercion val takes a Fin vertex to its natural-number value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("parameter", "conjParam", "The proposed broom parameter", ParameterFormula(),
                "Page 16 states: “Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).” The expression uses Nat.mod and Nat.div, with natural-number subtraction. At n = 19 the parameter is eight.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "Conjecture 5.4", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Page 16 states: “Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).” The formula includes both inequalities and both equality characterizations. Graph equality in the characterizations means isomorphism; Nonempty records existence of that isomorphism. The anonymous bracket specifies decidability of adjacency.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "Refutation at order nineteen", new Formula.Not(Parenthesized(ClaimBody())),
                "The tree broom 19 7 has spectral ratio strictly larger than broom 19 8. The upper Rayleigh inequality for its real Laplacian follows from RHLinalg.hermForm_le_of_eigenvalues_le with threshold equal to the largest ordered eigenvalue. A rational vector orthogonal to constants gives µ18(B₁₉⁷) < 35467/1000000, and a second rational vector gives 9018480/1000000 < µ1(B₁₉⁷). Positive rational LDL transpose factorizations give 39388/1000000 < µ18(B₁₉⁸) and µ1(B₁₉⁸) < 10014270/1000000. The integer products satisfy 355176114090 < 355219890240, so 10014270/39388 < 9018480/35467. Specializing the proposed upper bound to this tree contradicts those inequalities. This refutes the conjunction and does not refute its separate star lower bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("lwc-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula DotName(Formula value, string name) => Seq(Parenthesized(value), Dot, Op(name));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Op(name) : new Formula.Apply(Op(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => Seq(left, Plus, right);
    private static Formula Sub(Formula left, Formula right) => Parenthesized(Seq(left, Minus, right));
    private static Formula GraphBinders(Formula body) => All("n", Nat(), All("G", Call("SimpleGraph", FinN()),
        Seq(OpenBracket, Call("DecidableRel", DotName(V("G"), "Adj")), CloseBracket, Sp, body)));
    private static Formula Index(Formula value) => Seq(Langle, value, Rangle);

    private static Formula EigenvalueFormula()
    {
        Formula lap = App(DotName(V("G"), "lapMatrix"), new Formula.NamedConstant(FormulaIdentifier.Create("Real")));
        Formula eig = Seq(V("h"), Dot, new Formula.Subscript(Op("eigenvalues"), D(0)));
        return GraphBinders(All("i", FinN(), All("h", DotName(lap, "IsHermitian"),
            All("e", Parenthesized(Eqn(V("n"), QCall("Fintype", "card", FinN()))),
                Eqn(Call("lapEig", V("G"), V("i")), App(eig, QCall("Fin", "cast", V("e"), V("i"))))))));
    }
    private static Formula RatioFormula() => GraphBinders(Eqn(Call("spectralRatio", V("G")),
        Call("ite", Le(D(2), V("n")),
            new Formula.Fraction(Call("lapEig", V("G"), Index(D(0))),
                Call("lapEig", V("G"), Index(Sub(V("n"), D(2))))), D(0))));
    private static Formula BroomFormula()
    {
        Formula i = Call("val", V("i")), j = Call("val", V("j"));
        Formula relation = Or(And(Eqn(i, D(0)), And(Le(D(1), j), Le(j, Add(V("t"), D(1))))),
            And(Le(Add(V("t"), D(1)), i), Eqn(Add(i, D(1)), j)));
        Formula lambda = Seq(LambdaLower, Sp, Parenthesized(Seq(V("i"), Sp, V("j"), Sp, Colon, Sp, FinN())),
            Sp, Mapsto, Sp, Parenthesized(relation));
        return All("n", Nat(), All("t", Nat(), Eqn(Call("broom", V("n"), V("t")),
            QCall("SimpleGraph", "fromRel", Parenthesized(lambda)))));
    }
    private static Formula ParameterFormula() => All("n", Nat(), Eqn(Call("conjParam", V("n")),
        Call("ite", Eqn(QCall("Nat", "mod", V("n"), D(2)), D(1)),
            QCall("Nat", "div", Sub(V("n"), D(3)), D(2)), QCall("Nat", "div", Sub(V("n"), D(4)), D(2)))));
    private static Formula ClaimBody()
    {
        Formula ratio = Call("spectralRatio", V("T"));
        Formula star = QCall("SimpleGraph", "starGraph", Index(D(0)));
        Formula broom = Call("broom", V("n"), Call("conjParam", V("n")));
        Formula starRatio = Call("spectralRatio", star), broomRatio = Call("spectralRatio", broom);
        Formula leftEquality = Iff(Eqn(ratio, starRatio), Call("Nonempty", QCall("SimpleGraph", "Iso", V("T"), star)));
        Formula rightEquality = Iff(Eqn(ratio, broomRatio), Call("Nonempty", QCall("SimpleGraph", "Iso", V("T"), broom)));
        Formula conclusions = And(Le(starRatio, ratio), And(Le(ratio, broomRatio), And(leftEquality, rightEquality)));
        return All("n", Nat(), Imp(Le(D(8), V("n")), All("T", Call("SimpleGraph", FinN()),
            Seq(OpenBracket, Call("DecidableRel", DotName(V("T"), "Adj")), CloseBracket, Sp,
                Imp(DotName(V("T"), "IsTree"), conclusions)))));
    }
}
