using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class RSKMinimalInversionHankelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/pahuja2026minimalinversions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal matrices of RSK shape (8,8,1,1) cannot be Hankel.",
        H("A four-row refutation of Pahuja's Hankel conjecture"),
        Blocks(
            Paragraph(Text("A nonnegative integer matrix is a function Fin(n) → Fin(n) → ℕ. Indices and insertion letters start at zero. Adding one to every letter recovers the paper's positive letters without changing comparisons or row lengths. The integer sequence in the Hankel clause shifts its index by two relative to s₂,…,s₂ₙ. It is defined on all natural numbers; values at unused indices impose no condition.")),
            Node("insert-row", "Insertion into one row", "insertRow", InsertRow(),
                "Section 3.1, page 6: ‘If x₁ is greater than or equal to all entries in R₁, append x₁ at the end of R₁. Otherwise, let x₂ be the smaller entry in R₁ that is strictly greater than x₁. Replace x₂ by x₁, and the bumped entry x₂ is then inserted into the second row R₂.’ insertRow returns the modified row and the optional bumped letter. The recursion selects the leftmost entry strictly greater than x; equality passes to the next entry. A weakly increasing row makes this the entry specified by the paper."),
            Node("row-insert", "Bumping through successive rows", "rowInsert", RowInsert(),
                "Section 3.1, page 6: ‘This bumping process continues row by row until an entry is added at the end of some row Rₛ. The resulting tableau remains semistandard.’ rowInsert passes a bumped letter to the next row and stops when insertRow returns none. Lists contain rows in top-to-bottom order. The equations specify both Option constructors, with z denoting insertRow(x,r)."),
            Node("tableau", "The insertion tableau of a matrix word", "insertionTableau", Tableau(),
                "Section 3.1, page 6: ‘The RSK algorithm proceeds inductively through the insertion operation, where at each iteration, we obtain Pₖ by inserting jₖ into Pₖ₋₁, and recording iₖ in Qₖ₋₁ in the cell (s,t) where the new cell is added in Pₖ.’ insertionTableau keeps the insertion component P: List.foldl starts from [] and inserts letters from left to right. Recording Q is unnecessary for the common shape."),
            Node("word", "The bottom row of the generalised permutation", "readingWord", ReadingWord(),
                "Section 3, page 6: ‘A matrix M=(mᵢ,ⱼ) of size n × n can be written in a two-line notation as a generalised permutation by listing each pair (i,j) exactly mᵢ,ⱼ times. That is, we expand each entry of the matrix into repeated pairs.’ Page 6 also states: ‘In other words, the top row is weakly increasing, and two pairs with the same top entry have bottom entries in weakly increasing order.’ List.finRange enumerates each index ascending. The outer and inner List.flatMap implement this lexicographic order, and List.replicate supplies each multiplicity. readingWord denotes this matrix's bottom row, rather than the tableau row-word of Definition 3.5."),
            Node("shape", "RSK shape as row lengths", "shape", Shape(),
                "Section 1, page 1: ‘In this setting, the shape of a matrix is defined to be the common shape of the resulting pair of semistandard Young tableaux.’ The insertion component alone determines it: List.map List.length records the top-to-bottom row lengths. The partition condition is expressed separately by IsPartitionN."),
            Node("inversions", "The source inversion count", "inv", Inversions(),
                "Definition 3.1, page 6: ‘An inversion of a matrix M ∈ ℳλ is a pair of positions (i,j) and (k,l)} such that mᵢⱼ,mₖₗ > 0, and i < k and j > l.’ The following display gives the total ∑ᵢ<ₖ,ⱼ>ₗ mᵢ,ⱼ mₖ,ₗ. The formula sums over all four finite indices and selects precisely i < k and l < j; zero entries automatically contribute zero. No pairs with equal row indices contribute."),
            Node("minimal", "Minimum over all matrices of the same shape", "IsMinimal", Minimal(),
                "Section 1, page 2: ‘A matrix M ∈ ℳλ that attains this minimum will be called a minimal matrix of shape λ. This matrix need not be unique.’ The preceding sentence restricts the comparison to matrices of size n × n and shape λ. IsMinimal retains both the shape equation and comparison against every matrix M' on the same Fin(n) carrier."),
            Node("partition", "Exactly n positive partition parts", "IsPartitionN", Partition(),
                "Conjecture 1.1, page 2: ‘Let λ be a partition with n parts’. IsPartitionN requires length n, positivity of every part and nonincreasing order. List.Pairwise uses the relation x ≥ y; zero padding is excluded."),
            Node("claim", "Pahuja's Conjecture 1.1, both clauses", "claim", Claim(),
                "Conjecture 1.1, page 2: ‘Let λ be a partition with n parts, and let M=(mᵢ,ⱼ)₁≤ᵢ,ⱼ≤ₙ ∈ ℳλ be a minimal matrix of shape λ. Then M is symmetric, that is, mᵢ,ⱼ = mⱼ,ᵢ for all 1 ≤ i,j ≤ n. Moreover, every minimal matrix of shape λ is Hankel: there exists a sequence of integers s₂, s₃, …, s₂ₙ such that mᵢ,ⱼ = sᵢ₊ⱼ for all 1 ≤ i,j ≤ n.’ The quantified carriers are n : ℕ, lam : List ℕ and M : Fin(n) → Fin(n) → ℕ. The conjunction retains symmetry and Hankel, including the cast of M(i,j) to ℤ. Extending the finite integer sequence to ℕ → ℤ and shifting its indices by two is equivalent to the printed sequence. Every relevant index lies between zero and 2n−2."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The Hankel clause fails at shape (8,8,1,1)"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The symmetric matrix [[0,3,0,1],[3,0,2,0],[0,2,0,3],[1,0,3,0]] has shape [8,8,1,1] and inversion count 43. Insertion adds exactly one cell per letter, so a Hankel matrix of this shape has total weight 18. Its seven anti-diagonal parameters satisfy t₀+2t₁+3t₂+4t₃+3t₄+2t₅+t₆=18. All 2,743 nonnegative weighted tuples are enumerated, with the first parameter split into nineteen cases. Every tuple with the required shape has at least 45 inversions. Natural-valued inversion counts attain a minimum whenever the shape class is nonempty. Every minimizer therefore has at most 43 inversions and cannot be Hankel. This refutes the conjunction; it does not decide whether every minimizer is symmetric. The four-row example leaves the paper's two-row Theorem 4.1 outside the counterexample's range."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pahuja-2026-hankel-minimal-matrices"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Z => F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
    private static Formula ListN => Call("List", N);
    private static Formula Rows => Call("List", ListN);
    private static Formula FinN => Call("Fin", Id("n"));
    private static Formula MatrixN => new Formula.TypeArrow(FinN, new Formula.TypeArrow(FinN, N));
    private static Formula Empty => F.Seq(F.OpenBracket, F.CloseBracket);
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Exists(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Kw(string word) => F.Seq(F.Operatorname, F.Grp(F.Id(word)));
    private static Formula Qualified(string owner, string name) => F.Seq(Kw(owner), F.Dot, Kw(name));
    private static Formula Upstream(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Lambda(string variable, Formula type, Formula body) =>
        F.Seq(Parenthesized(F.Seq(Id(variable), F.Colon, type)), F.Mapsto, F.Sp, body);
    private static Formula Cons(Formula x, Formula xs) => F.Seq(x, F.Colon, F.Colon, xs);
    private static Formula List(Formula x) => F.Seq(F.OpenBracket, x, F.CloseBracket);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(F.Seq(x, F.Comma, y));
    private static Formula Field(Formula z, long index) => F.Seq(z, F.Dot, Num(index));
    private static Formula Parameters(Formula body) => All("n", N, All("M", MatrixN, body));
    private static Formula LetZ(Formula value, Formula body) => F.Seq(Kw("let"), Equal(Id("z"), value), F.Semi, body);
    private static Formula Sum(string variable, Formula type, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(Id(variable), F.Colon, type)), body);

    private static Formula InsertRow()
    {
        var x = Id("x"); var y = Id("y"); var ys = Id("ys"); var z = Id("z");
        var tail = LetZ(Call("insertRow", x, ys), Pair(Cons(y, Field(z, 1)), Field(z, 2)));
        var step = All("y", N, All("ys", ListN,
            Equal(Call("insertRow", x, Cons(y, ys)),
                F.Seq(Kw("if"), Lt(x, y), Kw("then"), Pair(Cons(x, ys), Call("some", y)), Kw("else"), tail))));
        return All("x", N, And(Equal(Call("insertRow", x, Empty), Pair(List(x), Id("none"))), step));
    }
    private static Formula RowInsert()
    {
        var x = Id("x"); var r = Id("r"); var rs = Id("rs"); var z = Id("z"); var y = Id("y");
        var cases = And(
            Imp(Equal(Field(z, 2), Id("none")), Equal(Call("rowInsert", x, Cons(r, rs)), Cons(Field(z, 1), rs))),
            All("y", N, Imp(Equal(Field(z, 2), Call("some", y)),
                Equal(Call("rowInsert", x, Cons(r, rs)), Cons(Field(z, 1), Call("rowInsert", y, rs))))));
        return All("x", N, And(Equal(Call("rowInsert", x, Empty), List(List(x))),
            All("r", ListN, All("rs", Rows, LetZ(Call("insertRow", x, r), cases)))));
    }
    private static Formula Tableau() => All("w", ListN,
        Equal(Call("insertionTableau", Id("w")), Upstream("List", "foldl",
            Lambda("T", Rows, Lambda("x", N, Call("rowInsert", Id("x"), Id("T")))), Empty, Id("w"))));
    private static Formula ReadingWord() => Parameters(Equal(Call("readingWord", Id("M")),
        Upstream("List", "flatMap", Lambda("i", FinN,
            Upstream("List", "flatMap", Lambda("j", FinN,
                Upstream("List", "replicate", Call("M", Id("i"), Id("j")), Call("val", Id("j")))),
                Upstream("List", "finRange", Id("n")))), Upstream("List", "finRange", Id("n")))));
    private static Formula Shape() => Parameters(Equal(Call("shape", Id("M")),
        Upstream("List", "map", Qualified("List", "length"), Call("insertionTableau", Call("readingWord", Id("M"))))));
    private static Formula Inversions()
    {
        var term = F.Seq(Kw("if"), And(Lt(Id("i"), Id("k")), Lt(Id("l"), Id("j"))), Kw("then"),
            Multiply(Call("M", Id("i"), Id("j")), Call("M", Id("k"), Id("l"))), Kw("else"), Num(0));
        return Parameters(Equal(Call("inv", Id("M")),
            Sum("i", FinN, Sum("k", FinN, Sum("j", FinN, Sum("l", FinN, Parenthesized(term)))))));
    }
    private static Formula Minimal()
    {
        var comparisons = All("Mprime", MatrixN,
            Imp(Equal(Call("shape", Id("Mprime")), Id("lam")),
                Le(Call("inv", Id("M")), Call("inv", Id("Mprime")))));
        var definition = Equal(Call("IsMinimal", Id("lam"), Id("M")),
            And(Equal(Call("shape", Id("M")), Id("lam")), comparisons));
        return All("n", N, All("lam", ListN, All("M", MatrixN, definition)));
    }
    private static Formula Partition() => All("n", N, All("lam", ListN,
        Equal(Call("IsPartitionN", Id("n"), Id("lam")),
            And(Equal(Upstream("List", "length", Id("lam")), Id("n")),
                And(All("x", N, Imp(Mem(Id("x"), Id("lam")), Lt(Num(0), Id("x")))),
                    Upstream("List", "Pairwise", Lambda("x", N, Lambda("y", N, Le(Id("y"), Id("x")))), Id("lam")))))));
    private static Formula Claim()
    {
        var symmetry = All("i", FinN, All("j", FinN,
            Equal(Call("M", Id("i"), Id("j")), Call("M", Id("j"), Id("i")))));
        var hankel = Exists("s", new Formula.TypeArrow(N, Z), All("i", FinN, All("j", FinN,
            Equal(Parenthesized(F.Seq(Call("M", Id("i"), Id("j")), F.Colon, Z)),
                Call("s", Add(Call("val", Id("i")), Call("val", Id("j"))))))));
        return Equal(Id("claim"), All("n", N, All("lam", ListN, All("M", MatrixN,
            Imp(Call("IsPartitionN", Id("n"), Id("lam")), Imp(Call("IsMinimal", Id("lam"), Id("M")),
                And(symmetry, hankel)))))));
    }
}
