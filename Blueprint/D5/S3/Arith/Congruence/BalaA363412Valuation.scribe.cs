using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BalaA363412ValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BalaA363412Valuation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2023sqrtminusthree");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer quadratic products and Bala's valuation conjectures.", H("BalaA363412Valuation"), Blocks(
            Node("claim", "The paired valuation conjecture", Eqn(Named("claim"), ClaimBody()),
                "OEIS A363412, FORMULA (revision 19, no page): \"Conjectures: 3 does not divide a(3*n+1) for all n; the 3-adic valuation v_3(a(3*n)) = v_3(a(3*n-1)) for all n.\" The second clause starts at n=1 so both source indices are nonnegative. The subtraction 3n-1 is natural truncated subtraction. The source sequence is BalaA363411.b.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The paired three-adic valuations agree", ClaimBody(),
                "At indices 3n and 3n-1, the reflection congruences express twice the imaginary coordinate as 3n times an integer prime to 3. For n at least one the factor 3n is nonzero. Multiplicativity of padicValInt removes the unit factors; both valuations equal padicValInt 3 (3n).", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala3634-paired-valuations"), ResolutionKind.Proved)))));

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
    private static Formula All(string variable, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subn(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Imp(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Rightarrow, Sp, Parenthesized(right));
    private static Formula ClaimBody() => All("n", N(), Imp(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, V("n")),
        Eqn(Call("padicValInt", D(3), App(Q("BalaA363411", "b"), Mul(D(3), V("n")))),
            Call("padicValInt", D(3), App(Q("BalaA363411", "b"), Subn(Mul(D(3), V("n")), D(1)))))));
}
