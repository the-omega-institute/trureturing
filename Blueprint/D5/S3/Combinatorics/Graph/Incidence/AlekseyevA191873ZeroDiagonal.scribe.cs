using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class AlekseyevA191873ZeroDiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/alekseyev2022a191873");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-diagonal and unrestricted rectangle-free maxima agree for n at least three.",
        H("Alekseyev's Zero-Diagonal Zarankiewicz Conjecture"),
        Blocks(
            Paragraph(Text("Binary matrices have entries in Fin 2. Rows and columns range independently over Fin n. "
                + "A rectangle uses two distinct rows and two distinct columns, with no adjacency requirement. "
                + "The least forcing count is restricted to counts at most n*n.")),
            Node("rectangle", "HasRectangle", "Four corners equal to one", RectangleFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "OEIS A072567, NAME (unpaginated): \"A variant of Zarankiewicz problem: maximal number of 1s in n X n 01-matrix with no four 1s forming a rectangle.\" The four corners are at i,j; i,j'; i',j; i',j'."),
            Node("diagonal-weights", "diagonalWeights", "Attainable zero-diagonal weights", DiagonalFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "OEIS A191873, NAME (unpaginated): \"A problem of Zarankiewicz: maximal number of 1's in an n X n matrix of 0's and 1's with 0's on the main diagonal and no \"rectangle\" with 1's at the four corners.\" The count is Finset.card of the entry positions equal to one; all main-diagonal entries are zero."),
            Node("forcing-counts", "forcingCounts", "Counts forcing a rectangle", ForcingFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "OEIS A001197, COMMENTS (unpaginated): \"a(n) is the minimum number k_2(n) such that any n X n matrix having that number of nonzero entries has a 2 X 2 submatrix with only nonzero entries. - _M. F. Hasler_, Sep 28 2021\" Fin 2 makes nonzero entries exactly the entries equal to one. The bound k ≤ n*n excludes impossible counts."),
            Node("claim", "claim", "The source conjecture", Disp(Equal(X("claim"), Parenthesized(ClaimBody()))),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "OEIS A191873, COMMENTS (unpaginated): \"Conjecture: for n >= 3, a(n) = A072567(n) = A001197(n) - 1 (per above comment). - _Max Alekseyev_, Jan 29 2022\" The witnesses d and k are respectively the attained greatest zero-diagonal weight and the attained least forcing count. SimpleGraph.zarankiewicz n n 2 2 is the unrestricted maximum. The final equality d+1=k expresses the source's subtraction without truncated subtraction."),
            Node("result", "result", "Equality in every dimension at least three", Disp(ClaimBody()),
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                "The proof uses a cyclic avoiding matrix of weight 2*n. A full row or column in an avoiding matrix has fewer than 2*n ones, so an extremizer has a zero in every row and column. A deficient Hall neighbourhood of zero entries would give four ones forming a rectangle; Hall therefore yields a permutation of zero entries. Permuting columns preserves the weight and places those zeros on the diagonal. Trimming an avoiding matrix to each smaller weight proves minimality of the forcing count. The argument does not require symmetry and makes no assertion about arbitrary prescribed diagonal patterns."))));

    private static DocumentBlock Node(string id, string name, string heading, Formula formula,
        AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("alekseyev-a191873"), ResolutionKind.Proved)
                : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Sp, Parenthesized(Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray())));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] clauses) =>
        Seq(clauses.SelectMany((a, i) => i == 0 ? new[] { Parenthesized(a) }
            : new[] { Sp, Land, Sp, Parenthesized(a) }).ToArray());
    private static Formula Not(Formula p) => Seq(Neg, Sp, p);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula FinN() => Call("Fin", X("n"));
    private static Formula MatrixN() => Call("Matrix", FinN(), FinN(), Call("Fin", D(2)));
    private static Formula Entry(Formula i, Formula j) => App(X("M"), i, j);
    private static Formula One(Formula i, Formula j) => Equal(Entry(i, j), D(1));
    private static Formula Weight()
    {
        Formula ij = X("ij"), pair = Seq(FinN(), Sp, Times, Sp, FinN());
        Formula predicate = Seq(Operatorname, Grp(X("fun")), Sp, ij, Colon, Sp, pair, Sp, Mapsto, Sp,
            One(Seq(ij, Dot, D(1)), Seq(ij, Dot, D(2))));
        Formula univ = Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Sp, Call("Finset", pair)));
        return App(Qualified("Finset", "card"), App(Qualified("Finset", "filter"), predicate, univ));
    }
    private static Formula RectangleFormula()
    {
        Formula body = And(Seq(X("i"), Sp, Neq, Sp, X("iPrime")),
            Seq(X("j"), Sp, Neq, Sp, X("jPrime")), One(X("i"), X("j")),
            One(X("i"), X("jPrime")), One(X("iPrime"), X("j")), One(X("iPrime"), X("jPrime")));
        body = Some("i", FinN(), Some("iPrime", FinN(), Some("j", FinN(), Some("jPrime", FinN(), body))));
        return Disp(All("n", Nat(), All("M", MatrixN(),
            Equal(Call("HasRectangle", X("M")), Parenthesized(body)))));
    }
    private static Formula DiagonalFormula() => Disp(All("n", Nat(),
        Equal(Call("diagonalWeights", X("n")), Seq(OpenBrace, Sp, X("w"), Colon, Sp, Nat(), Sp, Mid, Sp,
            Some("M", MatrixN(), And(Not(Call("HasRectangle", X("M"))),
                All("i", FinN(), Equal(Entry(X("i"), X("i")), D(0))), Equal(Weight(), X("w")))), Sp, CloseBrace))));
    private static Formula ForcingFormula() => Disp(All("n", Nat(),
        Equal(Call("forcingCounts", X("n")), Seq(OpenBrace, Sp, X("k"), Colon, Sp, Nat(), Sp, Mid, Sp,
            And(Seq(X("k"), Sp, Le, Sp, X("n"), Sp, Cdot, Sp, X("n")),
                All("M", MatrixN(), Seq(Parenthesized(Equal(Weight(), X("k"))), Sp, Implies, Sp,
                    Call("HasRectangle", X("M"))))), Sp, CloseBrace))));
    private static Formula ClaimBody() => All("n", Nat(),
        Seq(D(3), Sp, Le, Sp, X("n"), Sp, Implies, Sp, Some("d", Nat(), Some("k", Nat(),
            And(Call("IsGreatest", Call("diagonalWeights", X("n")), X("d")),
                Call("IsLeast", Call("forcingCounts", X("n")), X("k")),
                Equal(X("d"), App(Qualified("SimpleGraph", "zarankiewicz"), X("n"), X("n"), D(2), D(2))),
                Equal(Seq(X("d"), Plus, D(1)), X("k")))))));
}
