using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.ParticleProcesses;

internal sealed class AnnihilationMaximalDegeneracyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ayyermallick2010annihilation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At L = 5, alpha = 1/3 and beta = 2/5, the annihilation-process generator has an eigenspace of dimension at least two at eigenvalue -2, refuting the Ayyer–Mallick maximal-degeneracy conjecture.",
        H("Two eigenvectors at eigenvalue -2"),
        Blocks(
            Node("bulkMove", "A bulk transition", BulkMoveFormula(),
                "Ayyer–Mallick, Section II, p. 2, Eq. (1): \"10 → 01 with rate 1,\" \"11 → 00 with rate λ.\" At λ = 1, an occupied site is cleared and the next site is toggled. States are functions Fin L → Bool, with true denoting a particle; site 1 has index 0. The update expression also defines bulkMove when i and j coincide, although bulkCount uses only neighbouring distinct indices.", DescribeRole.Definition),
            Node("bulkCount", "Counting bulk transitions", BulkCountFormula(),
                "Ayyer–Mallick, Section II, p. 2, Eq. (1): \"10 → 01 with rate 1,\" \"11 → 00 with rate λ.\" At λ = 1, bulkCount adds one for each occupied site i with a right neighbour whose bulkMove gives t. The positive branch constructs the Fin L index from val(i)+1 and its bound h. ite is if-then-else.", DescribeRole.Definition),
            Node("leftCount", "Counting the left boundary flip", LeftCountFormula(),
                "Ayyer–Mallick, Section II, p. 2, Eq. (2): \"0 → 1 with rate α,\" \"1 → 0 with rate αλ.\" At λ = 1, both directions have rate α. When L is positive, leftCount is one precisely when flipping the first site gives t; otherwise it is zero.", DescribeRole.Definition),
            Node("rightCount", "Counting removal at the right boundary", RightCountFormula(),
                "Ayyer–Mallick, Section II, p. 2, Eq. (3): \"1 → 0 with rate β.\" When L is positive, rightCount is one precisely when the last site is occupied and clearing it gives t. Nat.sub is truncated natural-number subtraction. The last-site Fin index is constructed with the bound inferred from 0 < L; the proof of that bound is omitted from the mathematical notation.", DescribeRole.Definition),
            Node("offRate", "The total transition rate", OffRateFormula(),
                "Ayyer–Mallick, Section II, p. 2, Eqs. (1)–(3), at λ = 1: \"10 → 01 with rate 1,\" \"11 → 00 with rate λ,\" \"0 → 1 with rate α,\" \"1 → 0 with rate αλ,\" \"1 → 0 with rate β.\" The rate is the sum of all bulk and boundary contributions. Counts are cast from natural numbers to real numbers before addition and multiplication.", DescribeRole.Definition),
            Node("genMat", "The column-sum-zero generator", GenMatFormula(),
                "Ayyer–Strehl, Definition 1, p. 463 (PDF p. 3): \"A (continuous-time) transition matrix or Markov matrix or stochastic matrix is a square matrix of size equal to the cardinality of the configuration space whose (i, j)-th entry is given by the rate of the transition from configuration j to configuration i, when i is not equal to j. The (i, i)-th entry is then fixed by demanding that the entries in each column sum to zero.\" The column is the source state s and the row is the target state t. The diagonal is the negative sum of the rates to all other states.", DescribeRole.Definition),
            Node("claim", "The maximal-degeneracy assertion", ClaimFormula(),
                "Ayyer–Mallick, after Eq. (79), p. 14: \"We also conjecture that the Markov matrices are maximally undiagonalizable in the sense that each eigenvalue seems to have exactly one eigenvector independent of the number of times the eigenvalue appears (this implies that the Jordan blocks are of the maximum possible size). In other words, the degeneracy seems to be so strong that the Markov matrix M_L which is of size 2^L has only 2L eigenvectors.\" Ayyer–Strehl, Conjecture 1, p. 466 (PDF p. 6): \"The matrix M_L is maximally degenerate in the sense that it has exactly 2L eigenvectors.\" The claim is the geometric-multiplicity clause: every real eigenspace has dimension at most one for positive length and positive real rates. For numbers outside the spectrum the kernel has dimension zero. A real eigenvalue with a two-dimensional eigenspace also contradicts the unrestricted assertion.", DescribeRole.Definition),
            Node("result", "Refutation at length five", Disp(new Formula.Not(F.Id("claim"))),
                "At L = 5, alpha = 1/3 and beta = 2/5, write p(n) for the product over indices i < n of -1 when s(i) is true and 1 otherwise. The integer-valued functions v1 = p(1)p(2) - 3p(2) + 9p(1) - 5 and v2 = p(1)p(4) - p(2)p(3) - 3p(4) + 9p(3) - 27p(2) + 81p(1) - 40 yield two real left eigenvectors at -2. Their values are (2,20) at the empty state and (2,24) at the state occupied only at index 3; the nonzero minor proves independence. Exact rational matrix-vector equalities transfer to the real generator by casting. Rank equality with the transpose and rank–nullity give dimension at least two for the right eigenspace, contradicting claim.", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ayyer-mallick-2010-annihilation-maximal-degeneracy"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, bool derived = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("annihilation-" + (name switch
            {
                "bulkMove" => "bulk-move", "bulkCount" => "bulk-count",
                "leftCount" => "left-count", "rightCount" => "right-count",
                "offRate" => "off-rate", "genMat" => "gen-mat", _ => name,
            })),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula L) => Call("Fin", L);
    private static Formula States(Formula L) => new Formula.TypeArrow(FinOf(L), Named("Bool"));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula If(Formula cond, Formula yes, Formula no) => Seq(Named("if"), Sp, Parenthesized(cond), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula DepIf(Formula cond, Formula yes) => Seq(Named("if"), Sp, F.Id("h"), Colon, Parenthesized(cond), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, D(0));
    private static Formula SumOver(string v, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(v), Colon, type)), Sp, Parenthesized(body));
    private static Formula CastReal(Formula value) => Parenthesized(Seq(QCall("Nat", "cast", value), Colon, Real()));
    private static Formula WithStates(Formula body)
    {
        Formula L = F.Id("L");
        return All("L", Nat(), All("s", States(L), All("t", States(L), body)));
    }
    private static Formula WithRates(Formula body) => All("L", Nat(), All("alpha", Real(), All("beta", Real(), body)));

    private static Formula BulkMoveFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), i = F.Id("i"), j = F.Id("j");
        Formula body = QCall("Function", "update", QCall("Function", "update", s, i, Named("false")), j, QCall("Bool", "not", App(s, j)));
        return Disp(All("L", Nat(), All("s", States(L), All("i", FinOf(L), All("j", FinOf(L), Eq(Call("bulkMove", s, i, j), body))))));
    }
    private static Formula BulkCountFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), t = F.Id("t"), i = F.Id("i");
        Formula next = Add(Call("val", i), D(1));
        Formula moved = Call("bulkMove", s, i, QCall("Fin", "mk", next, F.Id("h")));
        Formula term = DepIf(Lt(next, L), If(And(Eq(App(s, i), Named("true")), Eq(t, moved)), D(1), D(0)));
        return Disp(WithStates(Eq(Call("bulkCount", L, s, t), SumOver("i", FinOf(L), term))));
    }
    private static Formula LeftCountFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), t = F.Id("t");
        Formula zero = QCall("Fin", "mk", D(0), F.Id("h"));
        Formula moved = QCall("Function", "update", s, zero, QCall("Bool", "not", App(s, zero)));
        return Disp(WithStates(Eq(Call("leftCount", L, s, t), DepIf(Lt(D(0), L), If(Eq(t, moved), D(1), D(0))))));
    }
    private static Formula RightCountFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), t = F.Id("t");
        Formula last = Seq(Langle, Sp, QCall("Nat", "sub", L, D(1)), Sp, Rangle);
        Formula moved = QCall("Function", "update", s, last, Named("false"));
        Formula body = If(Lt(D(0), L), If(And(Eq(App(s, last), Named("true")), Eq(t, moved)), D(1), D(0)), D(0));
        return Disp(WithStates(Eq(Call("rightCount", L, s, t), body)));
    }
    private static Formula OffRateFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), t = F.Id("t");
        Formula body = Add(Add(CastReal(Call("bulkCount", L, s, t)), Mul(F.Id("alpha"), CastReal(Call("leftCount", L, s, t)))), Mul(F.Id("beta"), CastReal(Call("rightCount", L, s, t))));
        return Disp(WithRates(All("s", States(L), All("t", States(L), Eq(Call("offRate", L, F.Id("alpha"), F.Id("beta"), s, t), body)))));
    }
    private static Formula GenMatFormula()
    {
        Formula L = F.Id("L"), s = F.Id("s"), t = F.Id("t"), u = F.Id("u");
        Formula sum = SumOver("u", States(L), If(Ne(u, s), Call("offRate", L, F.Id("alpha"), F.Id("beta"), s, u), D(0)));
        Formula body = If(Eq(t, s), Seq(Minus, Parenthesized(sum)), Call("offRate", L, F.Id("alpha"), F.Id("beta"), s, t));
        return Disp(WithRates(All("t", States(L), All("s", States(L), Eq(App(Call("genMat", L, F.Id("alpha"), F.Id("beta")), t, s), body)))));
    }
    private static Formula ClaimFormula()
    {
        Formula L = F.Id("L"), alpha = F.Id("alpha"), beta = F.Id("beta"), mu = F.Id("mu");
        Formula shifted = Sub(Call("genMat", L, alpha, beta), QCall("HSMul", "hSMul", mu, D(1)));
        Formula toLin = new Formula.Apply(Seq(Named("Matrix"), Dot, Operatorname, Grp(F.Id("toLin"), Apos)), [Parenthesized(shifted)]);
        Formula kernel = QCall("LinearMap", "ker", toLin);
        Formula bound = LeqOf(QCall("Module", "finrank", Real(), kernel), D(1));
        Formula body = All("L", Nat(), Imp(LeqOf(D(1), L), All("alpha", Real(), All("beta", Real(), Imp(Lt(D(0), alpha), Imp(Lt(D(0), beta), All("mu", Real(), bound)))))));
        return Disp(IffOf(F.Id("claim"), body));
    }
}
