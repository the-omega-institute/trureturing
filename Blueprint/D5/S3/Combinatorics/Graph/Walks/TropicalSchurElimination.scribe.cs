using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class TropicalSchurEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Min-plus vertex elimination preserves finite-walk distances for arbitrary extended nonnegative edge weights.",
        H("Tropical Schur elimination and pivot distances"),
        Blocks(
            Paragraph(Text("Let V be any vertex type and W assign an extended nonnegative real weight to every ordered pair. Infinity represents an unavailable edge. Walks are mathlib quiver paths in the complete directed quiver, with one arrow for each ordered pair. Vertices and edges may repeat; the empty walk has weight zero. The function weight sums edge weights, and distance is the infimum over all finite walks between the specified endpoints. Neither finiteness of V nor attainment of the infimum is assumed.")),
            Paragraph(Text("Fix a vertex b and write Pivots(V,b) for the subtype of vertices different from b. The map val includes this subtype into V. For pivot vertices a and z, the reduced weight schur(W,b)(a,z) is the minimum of W(val(a),val(z)) and W(val(a),b)+W(b,val(z)). Thus reduced walks exclude b at every vertex, including their endpoints.")),
            Describe.Lean(
                DescribeId.Create("pivot-walks-and-distance"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/TropicalSchurElimination.pivot_walks_and_distance"),
                H("Compression, exact expansion and equal distances"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each original walk between pivots compresses to a reduced walk of no larger weight. Each reduced walk expands to an original walk of exactly the same weight. Consequently the two infima agree, including when either is infinite.")),
                    Paragraph(Text("For expansion, choose a minimizing branch of each reduced edge: keep the original edge, or insert the two-edge detour through b. For compression, retain a walk ending at the most recent pivot. A visit to b is held as a pending final edge; the next pivot completes a reduced edge. Consecutive b-to-b loops can be discarded because their weights are nonnegative. Induction on the original quiver path gives the weight bound. Applying the two constructions to every walk gives the two inequalities between the infima.")),
                    Paragraph(Text("The result is the path interpretation of the min-plus update used in Floyd-Warshall elimination. It treats arbitrary vertex types and extended nonnegative weights directly. It makes no assertion for unrestricted signed weights: a negative loop at the eliminated vertex can lower original walk weights through arbitrarily many repetitions."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula v = F.Id("V"), w = F.Id("W"), b = F.Id("b");
        Formula a = F.Id("a"), z = F.Id("z"), p = F.Id("p"), q = F.Id("q");
        Formula original = Call("Walk", Call("val", a), Call("val", z));
        Formula reduced = Call("Walk", a, z);
        Formula s = Call("schur", w, b);
        Formula compression = All("p", original,
            ExistsBound("q", reduced, Le(Call("weight", s, q), Call("weight", w, p))));
        Formula expansion = All("q", reduced,
            ExistsBound("p", original, Eq(Call("weight", w, p), Call("weight", s, q))));
        Formula equality = Eq(Call("distance", s, a, z),
            Call("distance", w, Call("val", a), Call("val", z)));
        return Disp(All("V", Call("Type"),
            All("W", Arrow(v, Arrow(v, Call("ENNReal"))),
            All("b", v,
            All("a", Call("Pivots", v, b),
            All("z", Call("Pivots", v, b), And(compression, And(expansion, equality))))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsBound(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
}
