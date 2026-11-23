using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeCayleyCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting the cyclic vertices at an anchor transforms a target function into a rooted tree without changing its target multiset.",
        H("A Cayley code preserving targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("preserves-targets"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets"),
                H("The code preserves every target"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The code sends a function on the vertices other than the anchor to a rooted tree. It retains the arcs outside the cyclic core and replaces the core cycles by an anchor-first path to the root. A coordinate equivalence matches the original domain to the non-root vertices, including when the core is a singleton."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var a = F.Id("a");
        var i = F.Id("i");
        var f = F.Id("f");
        var code = At(Call("rootedCode", a), f);
        var coordinate = At(Call("codeCoordinates", a, f), i);
        var target = Call("parent", Call("snd", code), Call("fst", code), coordinate);
        var away = Call("Away", v, a);
        return All("V", F.Id("Type"), Seq(Instance("Finite", v), All("a", v,
            All("f", Arrow(away, v), All("i", away, Equal(target, At(f, i)))))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);
}
