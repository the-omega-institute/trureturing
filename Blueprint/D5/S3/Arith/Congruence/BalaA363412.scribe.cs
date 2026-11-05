using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BalaA363412Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BalaA363412.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2023sqrtminusthree");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer quadratic products and Bala's valuation conjectures.", H("BalaA363412"), Blocks(
            Node("claim", "Nondivisibility on the third residue class", Eqn(Named("claim"), ClaimBody()),
                "OEIS A363412, FORMULA (revision 19, no page): \"Conjectures: 3 does not divide a(3*n+1) for all n; the 3-adic valuation v_3(a(3*n)) = v_3(a(3*n-1)) for all n.\" The first clause concerns every natural n, including zero; the source sequence is BalaA363411.b.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Three never divides these terms", ClaimBody(),
                "The coordinate recursion modulo 3 has period 3. At 3n+1 its value is (1,1), so the imaginary coordinate is nonzero modulo 3.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala3634-nondivisibility"), ResolutionKind.Proved)),
            Node("reflection_congruences", "Two integer reflection congruences", ReflectionBody(),
                "For every finite integer coefficient family, a uniform shift by c changes the real coordinate by a multiple of 3c and the imaginary coordinate by c times the cardinality modulo 3c. Apply this to k mapped to m-k on 0 through m, and to m+1-k on 1 through m. Conjugation reverses the imaginary coordinate. The two displayed divisibilities follow and determine the paired three-adic valuations.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string variable, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Addn(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subn(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Dvd(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula ClaimBody() => All("n", N(), new Formula.Not(Parenthesized(Dvd(Cast(D(3), Z()), App(Q("BalaA363411", "b"), Addn(Mul(D(3), V("n")), D(1)))))));
    private static Formula ReflectionBody()
    {
        var m = V("m"); var z = Cast(m, Z());
        var difference = Subn(Mul(D(2), App(Q("BalaA363411", "b"), m)), Mul(z, Addn(z, D(1))));
        return All("m", N(), And(Dvd(Mul(D(3), z), difference), Dvd(Mul(D(3), Addn(z, D(1))), difference)));
    }
}
