using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class RectangularNilpotenceBarrierDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Mat(Formula r, Formula n, Formula m) => Call("Mat", r, n, m);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nilpotence depth cannot change by more than the number of rectangular exchanges.",
        H("Rectangular nilpotence barrier"), Blocks(
            Describe.Lean(DescribeId.Create("nilpotence-depth-bounds-chain-length"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.chain_depth_barrier"),
                H("A depth gap excludes short chains"),
                StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An elementary exchange has rectangular factors U and V, with potentially different intermediate dimensions. The identity (UV)^(j+1)=U(VU)^j V transfers every zero power with a cost of one exponent.")),
                    Paragraph(Text("Induction along the actual matrix chain bounds the two endpoint depths in both directions. The theorem retains every rectangular intermediate dimension and makes no essentiality assumption about intermediate matrices."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula r = F.Id("R"), n = F.Id("n"), m = F.Id("m");
        Formula a = F.Id("a"), b = F.Id("b"), l = F.Id("L");
        Formula x = F.Id("A"), y = F.Id("B");
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("R", F.Id("Type")), B("ringR", Call("Semiring", r)),
             B("n", F.Id("Nat")), B("m", F.Id("Nat")), B("a", F.Id("Nat")),
             B("b", F.Id("Nat")), B("L", F.Id("Nat")),
             B("A", Mat(r, n, n)), B("B", Mat(r, m, m)),
             B("chain", Call("ExchangeChain", r, x, y, l)),
             B("depthA", Call("ExactDepth", x, a)),
             B("depthB", Call("ExactDepth", y, b))],
            new Formula.Logic(
                new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,
                    new Formula.Binary(b, FormulaBinaryOperator.Add, l)),
                FormulaLogicOperator.And,
                new Formula.Relation(b, FormulaRelationOperator.LessThanOrEqual,
                    new Formula.Binary(a, FormulaBinaryOperator.Add, l))));
    }
}
