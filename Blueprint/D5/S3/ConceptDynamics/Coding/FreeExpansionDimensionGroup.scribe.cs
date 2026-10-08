using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FreeExpansionDimensionGroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FreeExpansionDimensionGroup.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => And(Implies(a, b), Implies(b, a));
    private static Formula Id(string name) => F.Id(name);
    private static Formula.BoundVariable[] GroupData => [
        B("H", Id("Type")), B("groupH", Call("Group", Id("H"))),
        B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat"))];
    private static Formula GroupMat => Call("GroupMat", Id("H"), Id("n"), Id("n"));
    private static Formula AdjacencyClaim => All(Equal(
        Call("coefficient", Call("vertexCoordinate", Call("apply", Call("transition", Id("A")),
            Call("vertex", Id("i"), Id("h"))), Id("j")), Id("t")),
        Call("castInt", Call("coefficient", Call("entry", Id("A"), Id("i"), Id("j")),
            Call("multiply", Call("inverse", Id("h")), Id("t"))))),
        [.. GroupData, B("A", GroupMat), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n"))),
         B("h", Id("H")), B("t", Id("H"))]);
    private static Formula InertClaim => All(Iff(Call("Inert", Id("A")), Call("Uniformizes", Id("A"))),
        [.. GroupData, B("A", GroupMat)]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original left group action on the actual integer free-expansion colimit is inert exactly when a positive natural power is uniform.",
        H("Free-expansion dimension-group inertness"), Blocks(
            Describe.Lean(DescribeId.Create("actual-free-expansion-adjacency"),
                DeclarationHandle.Create(Prefix + "actual_expansion_adjacency"), H("Ordered vertex coordinates"),
                StatementSource.FromAuthor(Disp(AdjacencyClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("VertexModule is Fin(n) to Z[H], the free abelian group on vertices (i,h). The vector vertex(i,h) has coefficient one at that vertex and zero elsewhere. The transition sends a row vector v to v times the coefficientwise integer cast of A. The displayed coefficient is exactly the number of actual expanded edges from (i,h) to (j,t): an edge labelled s ends at h*s, so s=h inverse times t. The order is retained for noncommutative H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-inertness-positive-uniformization"),
                DeclarationHandle.Create(Prefix + "inert_iff_uniformizes"), H("Identity on the actual stationary group"),
                StatementSource.FromAuthor(Disp(InertClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("DimensionGroup(A) is the actual stationary module colimit of this integer transition. The original left H-action sends each vertex (i,h) to (i,g*h), commutes with adjacency, and therefore induces groupAction(A,g) on that colimit. Inert(A) means groupAction(A,g) equals the identity for every g; uniformization is not part of this definition. Uniformizes(A) means that some positive natural exponent has all actual group coefficients constant in each matrix entry.")),
                    Paragraph(Text("The finite vertex basis and finite group give a common stage N at which T_A^N composed with every left translation equals T_A^N. Reading basis coefficients equates every coefficient of A^N; conversely uniform coefficients imply those stage equations on the basis. Advancing from N to N+1 supplies a positive exponent even when the common stage was zero. Inertness is identity on the underlying stationary group; the argument does not require a separately constructed ordered-group API or an order-unit normalization."))), DescribeRole.Theorem))));
}
