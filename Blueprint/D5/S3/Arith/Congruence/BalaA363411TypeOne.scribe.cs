using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BalaA363411TypeOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BalaA363411TypeOne.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2023sqrtminusthree");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer quadratic products and Bala's valuation conjectures.", H("BalaA363411TypeOne"), Blocks(
            Node("claim", "The type-one primes through 101", Eqn(Named("claim"), ClaimBody()),
                "OEIS A363411, COMMENTS (revision 18, no page): \"Type 1: primes that do not divide any element of the sequence {a(n)}.\" \"We conjecture that the set of type 1 primes begins {3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101, ...}.\" Here the initial list means exactly these primes through 101; the term index is unbounded.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The complete initial type-one list", ClaimBody(),
                "For each listed prime other than 3, the full coefficient block is (2,0) and its real coordinates below the prime are nonzero. Strong induction extends nonvanishing to every index. The real coordinate modulo 3 is always one. Each other prime at most 101 has a finite zero-coordinate certificate, including the prime 2.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala3634-type-one"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string variable, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Rightarrow, Sp, Parenthesized(right));
    private static Formula Dvd(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula ClaimBody()
    {
        var p = V("p"); var n = V("n");
        var listed = Seq(OpenBrace, D(3), Comma, Sp, D(1,1), Comma, Sp, D(1,7), Comma, Sp, D(2,3), Comma, Sp, D(2,9), Comma, Sp, D(4,1), Comma, Sp, D(4,7), Comma, Sp, D(5,3), Comma, Sp, D(5,9), Comma, Sp, D(8,3), Comma, Sp, D(8,9), Comma, Sp, D(1,0,1), CloseBrace);
        var nondivides = new Formula.Not(Parenthesized(Dvd(Cast(p, Z()), App(Q("BalaA363411", "a"), n))));
        var typeOne = And(App(Q("Nat", "Prime"), p), All("n", N(), nondivides));
        var iff = Seq(Parenthesized(typeOne), Sp, Leftrightarrow, Sp, p, Sp, InMacro, Sp, Cast(listed, Call("Finset", N())));
        return All("p", N(), Imp(new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, D(1,0,1)), iff));
    }
}
