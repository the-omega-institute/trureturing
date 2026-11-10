using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenSectorDocument : IScribeDocumentDefinition
{
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Then(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Bounds()
    {
        var rho = DefinitionDsl.Id("rho");
        var real = Call("re", rho);
        var square = new Formula.Power(Call("im", rho), N(2));
        var weight = Call("h14Weight", rho);
        var denominator = Add(Mul(N(72636), new Formula.Power(N(10), N(18))), N(763553532703907200));
        var lower = Div(N(345650537), denominator);
        var conclusion = new Formula.Logic(Less(N(0), weight), FormulaLogicOperator.And,
            Then(Le(square, N(196)), Le(lower, Mul(N(2), weight))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("rho"),
            Seq(Mathbb, Grp(FormulaDsl.Id("C"))),
            Then(Less(N(0), real), Then(Less(real, N(1)), Then(Less(N(100), square), conclusion))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-Pole Strip Kernel Comparison",
        H("Six-Pole Strip Kernel Comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteensector"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenSector.h14_kernel_bounds"),
            H("Six-Pole Strip Kernel Comparison"), StatementSource.FromAuthor(Disp(Bounds())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Here q=rho*(1-rho) and h14Weight(rho)=Re(1/(q*(q+30)*(q+56)*(q+90)*(q+132)*(q+182))). For every complex rho in the open strip with imaginary square above 100, the six-pole reciprocal kernel is positive. If the imaginary square is at most 196, twice its weight is at least 345650537/72636763553532703907200. The generic polar-angle and derivative proofs compare u and p on the closed auxiliary strip. The actual strip and height-ten premises are paid by the original exhaustive zero family at the final application; both signs and all multiplicities remain present."))),
            DescribeRole.Theorem))));
}
