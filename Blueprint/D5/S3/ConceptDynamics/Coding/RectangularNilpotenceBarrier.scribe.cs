using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class RectangularNilpotenceBarrierDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Mat(Formula r, Formula n, Formula m) => Call("Mat", r, n, m);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing a uniform component leaves a transient depth that cannot change by more than the number of rectangular exchanges.",
        H("Rectangular nilpotence barrier"), Blocks(
            Describe.Lean(DescribeId.Create("projected-nilpotence-depth-bounds-chain-length"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.projected_depth_barrier"),
                H("A transient-depth gap excludes short chains"),
                StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An elementary exchange has rectangular factors U and V, with potentially different intermediate dimensions. The identity (UV)^(j+1)=U(VU)^j V transfers every zero power with a cost of one exponent.")),
                    Paragraph(Text("Induction along the actual matrix chain bounds the two endpoint depths in both directions. Any additive and multiplicative coefficient projection preserves all rectangular products, even if it does not preserve one.")),
                    Paragraph(Text("The complement of a central idempotent is explicitly constructed as such a projection. Hence uniform components can be removed before applying the barrier. The theorem makes no essentiality assumption about intermediate matrices."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula r = F.Id("R"), s = F.Id("S"), n = F.Id("n"), m = F.Id("m");
        Formula a = F.Id("a"), b = F.Id("b"), l = F.Id("L");
        Formula x = F.Id("A"), y = F.Id("B"), f = F.Id("f");
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("R", F.Id("Type")), B("S", F.Id("Type")),
             B("ringR", Call("Semiring", r)), B("ringS", Call("Semiring", s)),
             B("f", Call("NonUnitalRingHom", r, s)),
             B("n", F.Id("Nat")), B("m", F.Id("Nat")), B("a", F.Id("Nat")),
             B("b", F.Id("Nat")), B("L", F.Id("Nat")),
             B("A", Mat(r, n, n)), B("B", Mat(r, m, m)),
             B("chain", Call("ExchangeChain", r, x, y, l)),
             B("depthA", Call("ExactDepth", Call("Matrix.map", x, f), a)),
             B("depthB", Call("ExactDepth", Call("Matrix.map", y, f), b))],
            new Formula.Logic(Call("LE.le", Call("HSub.hSub", a, b), l), FormulaLogicOperator.And,
                Call("LE.le", Call("HSub.hSub", b, a), l)));
    }
}
