using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HanWangYuGluingSpectrumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/hanwangyu2025gluing");
    private const string ChainsQuote = "Definition 8, page 10: \"For integers i = 1, 2, ⋯, k, let M_i = (S_i, A_i) be k Markov chains, and v_0^i be a fixed point in S_i. Assume θ = (θ_1, θ_2, ⋯, θ_k), 0 < θ_i < 1, and Σ_{i=1}^k θ_i = 1.\" ";
    private const string ClaimQuote = "Conjecture 1, §4.3, page 17: \"Glue Markov chains M_i = (S_i, A_i) to a Markov chain M = (S, A), then all the eigenvalues of A lie in the convex hull of the eigenvalues of all A_i on the complex plane.\" ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gluing two stochastic matrices yields an eigenvalue outside their spectral hull.",
        H("A counterexample to the Han–Wang–Yu spectral hull conjecture"),
        Blocks(
            Node("rooted", "RootedChain", "Finite chains with a selected root", RootedFormula(),
                ChainsQuote + "RootedChain has fields n, A and stochastic. Its states are Fin (n + 1), with selected root 0. The real matrix A is column stochastic: entry (v,w) is the transition probability from w to v. Source indices 1 through k become Fin k.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("glue", "glue", "The transition matrix after gluing", GlueFormula(),
                "Definition 8, page 10: \"The θ-gluing of M_i along v_0^i is the following Markov chain M = (S, A).\" The four cases give the source transition rule. The common root is none, and some ⟨i,v⟩ is state v.succ of input i. The transport h ▸ v changes the private index from chain i to chain j when h : i = j.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "claim", "The proposed spectral containment", Disp(IffOf(V("claim"), ClaimBody())),
                ClaimQuote + "The spectrum is taken over ℂ after applying algebraMap ℝ ℂ entrywise. The real convex hull lies in the complex plane. Every weight is strictly between zero and one and the weights sum to one.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "result", "The spectral containment fails", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take two copies of B = (1/54)[[43,9,2],[2,36,16],[9,9,36]], rooted at 0, with weights (1/2,1/2). Every column sums to one and every entry is nonnegative. The characteristic polynomial is (μ−1)(μ−17/27)(μ−1/2), so every input spectral value has real part at least 1/2. The glued vector (0,−4,3,4,−3) has eigenvalue 4/9: the private blocks have opposite signs and their contributions to the root row cancel. Convexity of the half-plane Re z ≥ 1/2 excludes 4/9 from the input spectral hull.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hwy-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula RootedFormula()
    {
        Formula n = V("n"), a = V("A"), index = Call("Fin", Add(n, D(1)));
        return Disp(Seq(Word("structure"), Sp, V("RootedChain"), Sp, Word("where"), Sp,
            OpenBrace, V("n"), Colon, Sp, Naturals(), Semi, Sp,
            a, Colon, Sp, Call("Matrix", index, index, Reals()), Semi, Sp,
            V("stochastic"), Colon, Sp, Member(a, Apply(Q("Matrix", "colStochastic"), Reals(), index)), CloseBrace));
    }

    private static Formula GlueFormula()
    {
        Formula k = V("k"), m = V("M"), theta = Theta, x = V("x"), y = V("y");
        Formula i = V("i"), j = V("j"), v = V("v"), w = V("w");
        Formula cases = Seq(Word("match"), Sp, x, Comma, Sp, y, Sp, Word("with"), Sp,
            Begin, Grp(V("cases")),
            V("none"), Comma, V("none"), Mapsto, Sp,
                SumAt("i", Call("Fin", k), Multiply(Apply(theta, i), Entry(m, i, D(0), D(0)))), RowBreak,
            Call("some", Pair(i, v)), Comma, V("none"), Mapsto, Sp,
                Multiply(Apply(theta, i), Entry(m, i, Field(v, "succ"), D(0))), RowBreak,
            V("none"), Comma, Call("some", Pair(j, w)), Mapsto, Sp,
                Entry(m, j, D(0), Field(w, "succ")), RowBreak,
            Call("some", Pair(i, v)), Comma, Call("some", Pair(j, w)), Mapsto, Sp,
                Word("if"), Sp, V("h"), Colon, Sp, Equal(i, j), Sp, Word("then"), Sp,
                Entry(m, j, Field(Apply(Q("Eq", "rec"), v, V("h")), "succ"), Field(w, "succ")),
                Sp, Word("else"), Sp, D(0), End, Grp(V("cases")));
        return Disp(All("k", Naturals(), All("M", Arrow(Call("Fin", k), V("RootedChain")),
            AllTheta(Arrow(Call("Fin", k), Reals()),
                All("x", State(m, k), All("y", State(m, k),
                    Equal(Call("glue", m, theta, x, y), cases)))))));
    }

    private static Formula ClaimBody()
    {
        Formula k = V("k"), m = V("M"), theta = Theta, i = V("i");
        Formula bounds = All("i", Call("Fin", k), And(LT(D(0), Apply(theta, i)), LT(Apply(theta, i), D(1))));
        Formula hull = Apply(V("convexHull"), Reals(), Parenthesized(Seq(
            Q("Set", "iUnion"), Sp, Parenthesized(Seq(Word("fun"), Sp, Typed(i, Call("Fin", k)), Sp, Mapsto, Sp, Spectrum(Field(Apply(m, i), "A")))))));
        return All("k", Naturals(), All("M", Arrow(Call("Fin", k), V("RootedChain")),
            AllTheta(Arrow(Call("Fin", k), Reals()), Imp(bounds,
                Imp(Equal(SumAt("i", Call("Fin", k), Apply(theta, i)), D(1)),
                    new Formula.Relation(Spectrum(Call("glue", m, theta)), FormulaRelationOperator.SubsetOf, hull))))));
    }

    private static Formula Spectrum(Formula a) => Apply(V("spectrum"), Complex(),
        Apply(Field(Parenthesized(a), "map"), Apply(V("algebraMap"), Reals(), Complex())));
    private static Formula State(Formula m, Formula k) => Call("Option", Call("Sigma",
        Parenthesized(Seq(Word("fun"), Sp, Typed(V("i"), Call("Fin", k)), Sp, Mapsto, Sp,
            Call("Fin", Field(Apply(m, V("i")), "n"))))));
    private static Formula Entry(Formula m, Formula i, Formula v, Formula w) => Apply(Field(Apply(m, i), "A"), v, w);
    private static Formula Field(Formula value, string field) => Seq(Parenthesized(value), Dot, Word(field));
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Pair(Formula first, Formula second) => Seq(Langle, Sp, first, Comma, Sp, second, Rangle);
    private static Formula Arrow(Formula from, Formula to) => Seq(Parenthesized(from), Sp, To, Sp, Parenthesized(to));
    private static Formula SumAt(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, body);
    private static Formula AllTheta(Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(Theta, type), Comma, Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => Apply(V(name), arguments);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
