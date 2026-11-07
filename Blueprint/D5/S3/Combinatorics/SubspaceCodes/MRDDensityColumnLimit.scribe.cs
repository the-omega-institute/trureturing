using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class MRDDensityColumnLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/gruica2023mrdcolumnlimit");
    private const string Question = @"Page 1082: “Problem 2.6. Compute or estimate \delta_q^{\mathrm{rk}}(n \times m, k, d). In particular, compute its asymptotic behavior as q \rightarrow +\infty. Compute or estimate the asymptotic density of MRD codes, i.e., \delta_q^{\mathrm{rk}}(n \times m, m(n-d+1),d), as q \rightarrow +\infty and as m \rightarrow +\infty.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-field column limit of maximum rank distance code density.",
        H("The column limit of MRD density"),
        Blocks(
            Node("claim", "The fixed-field column-limit assertion",
                Equal(X("claim"), Parenthesized(ClaimBody())), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                Question + " The field is a finite carrier K, q is Fintype.card K, n is the row count and m is the column count. The distance d satisfies 1 ≤ d ≤ n and n ≥ 2. The density uses the cardinalities of matrix subspaces; gaussian is the finite product of q-binomial factors and P is the infinite product. The assertion answers the fixed-field column-growth part of the question and includes d = 1."),
            Node("result", "The fixed-field MRD density formula", ClaimBody(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "Uniform sampling of image subspaces reduces the density to injectivity of a finite family of tensor restrictions. For distinct equal-dimensional left subspaces, every dependent tuple of frames has a strict tensor dimension surplus. Its contribution vanishes as the columns grow. Mixed Gaussian moments and finite multivariate Möbius truncation give the joint zero-kernel probability. Conditioning on injectivity then gives the density limit. When d = 1 the density equals one."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("mrd-column-limit-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody()
    {
        Formula field = X("K"), n = X("n"), d = X("d"), m = X("m");
        Formula cardinal = App(Q("Fintype", "card"), field);
        Formula value = Parenthesized(Seq(Word("if"), Sp, Equal(d, D(1)), Sp,
            Word("then"), Sp, D(1), Sp, Word("else"), Sp,
            new Formula.Power(Call("P", cardinal), Call("gaussian", cardinal, n,
                Parenthesized(Subtract(d, D(1)))))));
        Formula sequence = Parenthesized(Seq(Word("fun"), Sp, m, Colon, Nat, Sp, Mapsto, Sp,
            Call("density", field, n, m, Call("mrdDimension", n, m, d), d)));
        Formula limit = App(Word("Tendsto"), sequence, Q("Filter", "atTop"),
            App(Word("nhds"), value));
        return All("K", Word("Type"), Seq(OpenBracket, Call("Field", field), CloseBracket, Sp,
            OpenBracket, Call("Fintype", field), CloseBracket, Sp,
            All("n", Nat, All("d", Nat,
                Imp(Leq(D(2), n), Imp(Leq(D(1), d), Imp(Leq(d, n), limit)))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Word(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
