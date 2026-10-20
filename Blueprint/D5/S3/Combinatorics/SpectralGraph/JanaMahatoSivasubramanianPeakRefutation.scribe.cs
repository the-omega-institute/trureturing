using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class JanaMahatoSivasubramanianPeakRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/janamahatosivasubramanian2025steinerpeak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The path on sixteen vertices refutes the proposed Steiner coefficient peak.",
        H("The Steiner characteristic polynomial peaks beyond n minus one"),
        Blocks(
            Node("steiner", "Steiner distance on a path", SteinerFormula(),
                "Page 3 states: “the entry of 𝔇_2(T) corresponding to the row {i,j} and column {k,l} is the minimum number of edges among all connected subtrees of T whose vertex set contains the four vertices i, j, k and l.” On the path with vertices 1 through n, connected subtrees are intervals from a to b and have b−a edges. The infimum is taken in Nat; all subtraction below is natural subtraction."),
            Node("basis", "The ordered path basis", BasisFormula(),
                "Remark 23, page 14, states: “Let P_n be the path on n vertices with edges e_i = {i, i+1} for i = 1, …, n−1. Let B = (e_1, f_1, e_2, f_2, …, e_{n−2}, f_{n−2}, e_{n−1}) be the ordered basis for the row space of 𝔇_2(P_n) where f_j = {j, j+2}, for j = 1, …, n−2.” Even zero-based indices enumerate the edges e_i and odd indices enumerate the pairs f_j. Nat.div and Nat.mod denote integer quotient and remainder."),
            Node("D", "The principal Steiner distance matrix", MatrixFormula(),
                "Page 14 states: “We denote by 𝔇_{P_n} the matrix 𝔇_2(P_n)[B, B], that is, 𝔇_{P_n} := 𝔇_2(P_n)[B, B].” Its integer entry is the Steiner distance of the union of the row and column pairs; repeated vertices are counted only once."),
            Node("claim", "Conjecture 29", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Conjecture 29, page 18, states: “For a path P_n on n > 5 vertices, if CharPoly_{𝔇_{P_n}}(x) = Σ_{i=0}^{2n−3} a_i x^i and |a_ℓ| = max{|a_0|, |a_1|, …, |a_{2n−4}|}, then ℓ = n − 1.” Matrix.charpoly is det(xI−D); the quantified inequalities express attainment of the maximum over precisely the nonleading coefficients, from zero through 2n−4."),
            Node("result", "Refutation at sixteen vertices", new Formula.Not(Parenthesized(ClaimBody())),
                "For n=16, the coefficient magnitudes at indices 15 and 16 are 939602445008 and 956326515118. The latter dominates all coefficients at indices zero through 28, while 16 differs from 16−1. The exact coefficient vector in ascending order is (−15, −813, −20869, −337481, −3858223, −33170333, −222721740, −1197384332, −5242633806, −18915546250, −56691343231, −141862420523, −297217763703, −521743703045, −766504605632, −939602445008, −956326515118, −802497798666, −549972018662, −304018467998, −133385920554, −45480785950, −11720987416, −2198470872, −284539268, −23452364, −1076103, −20755, −43, 1). The interval formula evaluates the matrix entries. An integer matrix K satisfies A K = K C for the coefficient companion matrix C, and a left inverse of K modulo seven proves its determinant nonzero. Characteristic-polynomial invariance and the coefficient multiplication theorem then identify the polynomial. This refutes the proposed exact peak; it leaves the source's upper bound and its separate coefficient identities unaffected. The exact peak for unbounded n remains an open question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jana-mahato-sivasubramanian-2025-steiner-path-peak"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("jms-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Call("Nat");
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            App(Seq(Operatorname, Grp(V(name))), arguments);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Sub(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);
    private static Formula Size(Formula n) => Sub(Seq(D(2), Sp, Cdot, Sp, n), D(3));
    private static Formula Ceiling(Formula n) => Sub(Seq(D(2), Sp, Cdot, Sp, n), D(4));
    private static Formula Fin(Formula n) => Call("Fin", Parenthesized(Size(n)));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Coeff(Formula n, Formula i) =>
        App(Q("Polynomial", "coeff"), App(Q("Matrix", "charpoly"), Call("D", n)), i);

    private static Formula ClaimBody()
    {
        Formula n = V("n"), ell = V("ell"), i = V("i");
        return All("n", Nat(), Imp(Less(D(5), n), All("ell", Nat(),
            Imp(Leq(ell, Ceiling(n)), Imp(All("i", Nat(),
                Imp(Leq(i, Ceiling(n)), Leq(Abs(Coeff(n, i)), Abs(Coeff(n, ell))))),
                Eqn(ell, Sub(n, D(1))))))));
    }

    private static Formula SteinerFormula()
    {
        Formula n = V("n"), s = V("S"), k = V("k"), a = V("a"), b = V("b"), v = V("v");
        Formula conditions = And(Leq(D(1), a), And(Leq(a, b), And(Leq(b, n),
            And(Eqn(Sub(b, a), k), All("v", Nat(), Imp(Member(v, s), And(Leq(a, v), Leq(v, b))))))));
        Formula set = Seq(OpenBrace, Sp, k, Colon, Sp, Nat(), Sp, Mid, Sp,
            Ex("a", Nat(), Ex("b", Nat(), conditions)), Sp, CloseBrace);
        return All("n", Nat(), All("S", Call("Finset", Nat()),
            Eqn(Call("steiner", n, s), Call("sInf", set))));
    }

    private static Formula BasisFormula()
    {
        Formula n = V("n"), t = V("t"), val = Call("val", t);
        Formula half = App(Q("Nat", "div"), val, D(2));
        Formula start = Add(half, D(1));
        Formula evenPair = Seq(OpenBrace, Sp, start, Comma, Sp, Add(half, D(2)), Sp, CloseBrace);
        Formula oddPair = Seq(OpenBrace, Sp, start, Comma, Sp, Add(half, D(3)), Sp, CloseBrace);
        Formula body = Seq(Call("if"), Sp, Eqn(App(Q("Nat", "mod"), val, D(2)), D(0)), Sp,
            Call("then"), Sp, evenPair, Sp, Call("else"), Sp, oddPair);
        return All("n", Nat(), All("t", Fin(n), Eqn(Call("basis", n, t), body)));
    }

    private static Formula MatrixFormula()
    {
        Formula n = V("n"), t = V("t"), u = V("u");
        Formula union = Seq(Call("basis", n, t), Sp, Cup, Sp, Call("basis", n, u));
        Formula value = Parenthesized(Seq(Call("steiner", n, union), Colon, Sp, Call("Int")));
        Formula body = Seq(Call("fun"), Sp, t, Colon, Sp, Fin(n), Comma, Sp,
            u, Colon, Sp, Fin(n), Sp, Mapsto, Sp, value);
        return All("n", Nat(), Eqn(Seq(Call("D", n), Colon, Sp,
            Call("Matrix", Fin(n), Fin(n), Call("Int"))), Parenthesized(body)));
    }
}
