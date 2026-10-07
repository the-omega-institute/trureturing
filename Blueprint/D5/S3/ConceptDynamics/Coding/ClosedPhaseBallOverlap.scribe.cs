using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class ClosedPhaseBallOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed phase balls intersect exactly at the doubled-radius distance bound.",
        H("Closed Circular Phase Ball Overlap"),
        Blocks(Describe.Lean(DescribeId.Create("closed-phase-ball-overlap"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ClosedPhaseBallOverlap.closed_phase_ball_overlap"),
            H("Exact closed-ball intersection"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "For a natural period P and a real radius eps, two closed balls in the real "
                + "additive circle meet exactly when their centers have distance at most 2eps. "
                + "The triangle inequality gives necessity. For sufficiency, choose a shortest "
                + "lift of the displacement and take its midpoint. Equality is included."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Q(string names, Formula type, Formula body)
    {
        var binders = names.Split(' ');
        for (var i = binders.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, V(binders[i]), Colon, Sp, Par(type), Comma, Sp, Par(body));
        return body;
    }
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, Par(type), Comma, Sp, Par(body));
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula IffF(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] parts)
    {
        var result = parts[parts.Length - 1];
        for (var i = parts.Length - 2; i >= 0; i--) result = Seq(Par(parts[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Statement()
    {
        var p = V("P"); var eps = V("eps"); var x = V("x"); var y = V("y"); var q = V("q");
        var circle = Call("AddCircle", Call("real", p));
        return Disp(Q("P", N, Q("eps", R, Q("x y", circle,
            IffF(Ex("q", circle, And(Leq(Call("dist", q, x), eps), Leq(Call("dist", q, y), eps))),
                Leq(Call("dist", x, y), Mul(D(2), eps)))))));
    }
}
