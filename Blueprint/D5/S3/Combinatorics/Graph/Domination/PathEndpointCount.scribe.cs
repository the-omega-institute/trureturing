using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class PathEndpointCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Path endpoints and the original restricted family", H("Path endpoints and the original restricted family"), Blocks(
            Node("restricted", "Restricted actual family", "restrictedFamily", "Maximal independent subsets omitting at least one of the two endpoints. Complementation corresponds to a minimal vertex cover containing at least one endpoint.", DescribeRole.Definition),
            Node("caps", "Both endpoints", "both_count", "For every n, the maximal independent subsets of a path of order n+4 containing both endpoints are in bijection with unrestricted maximal independent subsets of order n. The middle restriction and endpoint insertion are actual inverses, including the empty middle at n=0.", DescribeRole.Theorem),
            Node("partition", "Exact endpoint partition", "restricted_complement", "The allowed family and the forbidden endpoint family partition all subsets at every order n+4. This is a sum of actual cardinalities, without relying on extrapolation.", DescribeRole.Theorem),
            Node("initial", "The complete source zero prefix", "restricted_initial", "The restricted count is zero at orders zero, one and two, and one at order three. The order-three family is proved to be exactly the singleton family containing the subset {1}.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Presentation(declaration), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static StatementSource Presentation(string name)
    {
        Formula n = V("n");
        Formula M(Formula k) => Call("count", k);
        Formula R(Formula k) => Call("restrictedCount", k);
        Formula? f = name switch
        {
            "both_count" => All("n", Nat, Eq(Call("card", Call("bothFamily", Add(n, D(4)))), M(n))),
            "restricted_complement" => All("n", Nat, Eq(Add(R(Add(n, D(4))), M(n)), M(Add(n, D(4))))),
            "restricted_initial" => And(Eq(R(D(0)), D(0)), And(Eq(R(D(1)), D(0)), And(Eq(R(D(2)), D(0)), Eq(R(D(3)), D(1))))),
            _ => null
        };
        return f is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(f));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
