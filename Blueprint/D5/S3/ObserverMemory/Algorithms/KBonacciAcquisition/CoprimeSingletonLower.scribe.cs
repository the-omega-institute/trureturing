using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class CoprimeSingletonLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var Y = F.Id("Y"); var k = F.Id("k"); var m = F.Id("m"); var j = F.Id("j");
        var A = F.Id("A"); var B = F.Id("B"); var v = F.Id("v"); var a = F.Id("a");
        var phi = F.Id("phi"); var i = F.Id("i"); var t = F.Id("t");
        var bits = F.Id("bits"); var n = F.Id("n"); var tree = F.Id("tree");
        var s = F.Id("s"); var marker = F.Id("marker"); var none = F.Id("none");
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var boolType = F.Id("Bool");
        var phaseType = Call("ZMod", Add(k, D(1))); var valueType = Call("ZMod", D(2));
        var edge = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("phi"), phaseType,
            Equal(Call("coefficient", k, phi),
                Add(new Formula.Apply(marker, [phi]), new Formula.Apply(marker, [Add(phi, D(1))]))));
        var indexed = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("i"), nat), new(FormulaIdentifier.Create("t"), nat)],
            new Formula.Logic(new Formula.Relation(i, FormulaRelationOperator.LessThanOrEqual, k),
                FormulaLogicOperator.Implies, new Formula.Logic(
                    new Formula.Relation(t, FormulaRelationOperator.LessThanOrEqual, k),
                    FormulaLogicOperator.Implies, Equal(
                        new Formula.Apply(marker, [Add(new Formula.Negate(Call("cast", i, phaseType)),
                            Call("cast", t, phaseType))]), Call("ite", Equal(t, i), D(1), D(0))))));
        var absorbed = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("bits"), Call("List", boolType),
            Equal(Call("runWord", Call("bitUpdate", k), bits, none), none));
        var record = Call("some", Seq(Open, v, Comma,
            new Formula.Negate(Call("cast", i, phaseType)), Comma, s, Close));
        var correct = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("i"), nat), new(FormulaIdentifier.Create("s"), nat)],
            new Formula.Logic(new Formula.Relation(i, FormulaRelationOperator.LessThanOrEqual, k),
                FormulaLogicOperator.Implies, new Formula.Logic(
                    new Formula.Relation(s, FormulaRelationOperator.LessThan, k),
                    FormulaLogicOperator.Implies,
                    Equal(Call("result", tree, record), Call("ite", Equal(i, j), B, A)))));
        var lower = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("n"), nat),
             new(FormulaIdentifier.Create("tree"), Call("AcquisitionTree", k, m, a, Y, n))],
            new Formula.Logic(correct, FormulaLogicOperator.Implies,
                new Formula.Relation(Call("max", D(2), Call("ceilDiv", j, m)),
                    FormulaRelationOperator.LessThanOrEqual, n)));
        var conclusion = new Formula.Logic(edge, FormulaLogicOperator.And,
            new Formula.Logic(indexed, FormulaLogicOperator.And,
                new Formula.Logic(absorbed, FormulaLogicOperator.And, lower)));
        var markerFunction = Seq(Open, LambdaLower, Sp, Open, phi, Colon, phaseType, Close,
            Comma, Sp, Call("ite", Equal(phi, D(0)), D(1), D(0)), Close);
        var localConclusion = Seq(Operatorname, Grp(F.Id("let")), Sp, marker, Eq,
            markerFunction, Sp, Operatorname, Grp(F.Id("in")), Sp, Open, conclusion, Close);
        var hypotheses = new List<Formula>
        {
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, k),
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            new Formula.Relation(m, FormulaRelationOperator.LessThan, k),
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, j),
            new Formula.Relation(j, FormulaRelationOperator.LessThanOrEqual, k), NotEqual(A, B)
        };
        Formula assumptions = hypotheses[^1];
        for (var x = hypotheses.Count - 2; x >= 0; x--)
            assumptions = new Formula.Logic(hypotheses[x], FormulaLogicOperator.And, assumptions);
        var statement = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("Y"), F.Id("Type")),
             new(FormulaIdentifier.Create("k"), nat), new(FormulaIdentifier.Create("m"), nat),
             new(FormulaIdentifier.Create("j"), nat), new(FormulaIdentifier.Create("A"), Y),
             new(FormulaIdentifier.Create("B"), Y), new(FormulaIdentifier.Create("v"), valueType),
             new(FormulaIdentifier.Create("a"), boolType)],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, localConclusion));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Binary initial phase singletons require two complete blocks and paid arrival.",
            H("The obstruction to acquiring a binary phase singleton"),
            Blocks(Describe.Lean(
                DescribeId.Create("singleton-tree-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/"
                    + "CoprimeSingletonLower.singleton_tree_obstruction"),
                H("Every correct endpoint tree has horizon at least max(2,ceil(j/m))"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary Y, distinct labels A and B, value v in ZMod(2), "
                        + "either alphabet, k>=2, 2<=m<k and 1<=j<=k, every tree that "
                        + "labels all initial records (v,-i,s) with i<=k and s<k by B "
                        + "exactly when i=j has horizon n>=max(2,ceil(j/m)). No "
                        + "coprimality assumption or separate survival premise is needed.")),
                    Paragraph(Text(
                        "The marker is the indicator of zero phase with values in ZMod(2). "
                        + "Its adjacent sum is the literal coefficient; at phase -i+t "
                        + "for i,t<=k it is the indicator of t=i. Rejection is absorbing "
                        + "for every Boolean word. The casts in the formula take values "
                        + "in ZMod(k+1), and all marker arithmetic takes values in ZMod(2).")),
                    Paragraph(Text("The literal transitions are those of "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel"),
                        Text(" and the trees have the endpoint semantics of "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells"),
                        Text(". A first bit equal to one would reject every record with "
                            + "tail k-1, so a correct tree starts with zero. Before arrival "
                            + "at j, the zero and target phases have identical observations "
                            + "and archives, forcing the arrival bound. A one-block singleton "
                            + "would have total increment one, whereas adjacent marker "
                            + "cancellation makes that total zero. This forces two blocks."))),
                DescribeRole.Theorem))));
    }
}
