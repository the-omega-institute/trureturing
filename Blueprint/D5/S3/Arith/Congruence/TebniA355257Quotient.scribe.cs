using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TebniA355257QuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/TebniA355257Quotient.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/luschnytebni2022a355257");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For even n and prime p, the quotient A(n,p)/(p-1) is an integer congruent to one modulo p.",
        H("Tebni's prime quotient congruence"),
        Blocks(
            Node("claim", "The source quotient conjecture", Eq(V("claim"), Parenthesized(ClaimBody())),
                "OEIS A355257, revision 37, COMMENTS (unpaginated): "
                + "\"Conjecture: For p prime and n even, (A(n, p) / (p - 1)) == 1 (mod p).\" "
                + "The quotient is taken in Q. An integer q equal to that quotient expresses its integrality; "
                + "Int.ModEq has integer modulus p. The row index is a natural number, including zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The quotient congruence holds", ClaimBody(),
                "The shared coefficient sum is divisible by p-1 for even n. Its residue modulo p is minus one. "
                + "Writing that integer as (p-1)q and reducing modulo p gives -q=-1, hence q=1 modulo p.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tebni355257-quotient"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("tebni355257-quotient-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimBody()
    {
        var n = V("n"); var p = V("p"); var q = V("q");
        var quotient = new Formula.Fraction(Qualified("TebniA355257Divisibility", "A", n, p),
            Parenthesized(Sub(Cast(p, QType()), D(1))));
        return All("n", N(), All("p", N(), Imp(Qualified("Nat", "Prime", p), Imp(Call("Even", n),
            Ex("q", ZType(), And(Eq(Cast(q, QType()), quotient),
                Qualified("Int", "ModEq", Cast(p, ZType()), q, D(1))))))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Named(owner), Dot, Named(name)), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula ZType() => Seq(Mathbb, Grp(V("Z")));
    private static Formula QType() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
