using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PowerGraphs;

internal sealed class SilveiraContrerasTorsionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/silveiracontreras2026powergraph");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A torsion group with cyclic center has a disconnected proper generalized power graph.",
        H("A disconnected proper generalized power graph"),
        Blocks(
            Paragraph(Text("The vertices of P(G) are the nonidentity elements of G. Distinct vertices x and y are adjacent if a finite list of elements g of G gives y as the ordered product of g⁻¹xg, or gives x as the ordered product of g⁻¹yg. The empty product is the identity and hence cannot produce a proper vertex.")),
            Describe.Lean(DescribeId.Create("silveira-contreras-torsion-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The torsion-group assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("claim"), FormulaRelationOperator.Equal, Paren(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Problem 4.3 asks whether Theorem 4.2(2) remains true with torsion in place of finiteness. Here torsion means every element has finite order, Z(G) is the group center, and the extended diameter is the supremum of pairwise extended graph distances."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("silveira-contreras-torsion-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation by an isolated central involution"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Paren(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Start with the trivial group and iterate regular wreath products by C₂. Embed each stage in the coordinate indexed by the identity. Each stage is a finite 2-group, so every element of the direct limit H has finite order. In the next stage the nonidentity shift moves every embedded nonidentity element. Since the stage maps are injective, the shifted element is distinct in H, so H has trivial center.")),
                    Paragraph(Text("For a nonidentity a in H, lift a and a finite list of conjugators to one stage. In that finite 2-group, pass to the quotient by the first lower central series term omitting a. The image of a is central, nonidentity, and of even order. The product of an odd number of conjugates has image an odd power of a's image and cannot equal the identity.")),
                    Paragraph(Text("The center of H × C₂ is the second factor. Let c be the nonidentity element of C₂. Products of conjugates of (1,c) are powers of (1,c), giving no outgoing edge. A product from a distinct proper vertex to (1,c) would have to start with a vertex (a,c) and have odd length by its second coordinate. Its first coordinate would give an odd product of conjugates of a ≠ 1 equal to the identity. Thus (1,c) has no incoming edge either. The image of the first-stage shift, paired with 1, is a second proper vertex. A walk to it would require a first edge at (1,c)."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("silveira-contreras-2026-torsion-powergraph"),
                    ResolutionKind.Refuted)))));

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula ClaimBody()
    {
        Formula g = V("G"), x = V("x");
        Formula graph = Call("P", g);
        Formula torsion = All("x", g, Call("IsOfFinOrder", x));
        Formula cyclic = Call("IsCyclic", Call("Z", g));
        Formula bound = new Formula.Relation(Call("ediam", graph),
            FormulaRelationOperator.LessThanOrEqual, D(4));
        Formula conclusion = new Formula.Logic(Call("Connected", graph),
            FormulaLogicOperator.And, bound);
        return All("G", Call("Type"), Seq(OpenBracket, Call("Group", g), CloseBracket, Sp,
            Implies(Paren(torsion), Implies(cyclic, Paren(conclusion)))));
    }
}
