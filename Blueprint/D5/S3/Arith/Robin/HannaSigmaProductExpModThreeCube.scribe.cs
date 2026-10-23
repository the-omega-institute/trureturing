using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class HannaSigmaProductExpModThreeCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/HannaSigmaProductExpModThreeCube.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382124a382125");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cube has the characteristic-three coefficient pattern at every index.",
        H("Hanna's Cubed Sigma-Product Exponential"),
        Blocks(
            Node("claim", "The A382125 congruences", Seq(Call("claim"), Sp, Iff, Sp, P(ClaimBody())),
                "Conjectures: a(3*n) == A382124(n) (mod 3) for n >= 0; a(3*n+1) == 0 (mod 3) and a(3*n+2) == 0 (mod 3) for n >= 0. OEIS A382125, COMMENT (unpaginated). A and B are the rational generating functions defined in HannaSigmaProductExpModThree; all coefficient witnesses are integers.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "All three coefficient classes", ClaimBody(),
                "The first congruence is the symmetric A382124 congruence. The other two follow from the characteristic-three coefficient pattern of the integer lift cubed.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannasigmaproductexpmodthreecube-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula P(Formula value) => Parenthesized(value);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Cast(Formula a, Formula type) => P(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(P(a), Sp, Land, Sp, P(b));
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula Mod(Formula a, Formula b) => Seq(a, Sp, Equiv, Sp, b, Sp, Pmod, Grp(D(3)));
    private static Formula ClaimBody()
    {
        var n = V("n");
        var u = V("u");
        var v = V("v");
        var first = All("n", N(), Ex("u", Z(), Ex("v", Z(),
            And(Eqn(Coeff(Mul(D(3), n), Call("B")), Cast(u, Q())),
                And(Eqn(Coeff(n, Call("A")), Cast(v, Q())), Mod(u, v))))));
        var second = All("n", N(), Ex("u", Z(), Ex("v", Z(),
            And(Eqn(Coeff(Add(Mul(D(3), n), D(1)), Call("B")), Cast(u, Q())),
                And(Eqn(Coeff(Add(Mul(D(3), n), D(2)), Call("B")), Cast(v, Q())),
                    And(Mod(u, D(0)), Mod(v, D(0))))))));
        return And(first, second);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
