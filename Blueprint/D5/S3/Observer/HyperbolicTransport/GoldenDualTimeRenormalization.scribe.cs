using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HyperbolicTransport;

internal sealed class GoldenDualTimeRenormalizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization."
            + "golden_dual_time_renormalization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden reciprocal time scaling preserves the dual product and is reversed by reflection.",
        H("Golden Dual-Time Renormalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-dual-time-renormalization"),
            DeclarationHandle.Create(Declaration),
            H("Reciprocal scaling preserves the product and reflection reverses time"),
            StatementSource.FromAuthor(RenormalizationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set a=phi^2. The update contracts the transverse scale delta by a inverse "
                        + "and expands the observation length L by a, so their product is fixed.")),
                Paragraph(Text(
                    "The coordinate exchange J conjugates the diagonal update R to the displayed "
                        + "reverse matrix. Lean also checks both matrix products with that reverse "
                        + "are the identity, making the inverse claim explicit.")),
                Paragraph(Text(
                    "The theorem records only this self-contained two-coordinate algebra. It does "
                        + "not assert that every observer duality is golden or derive the separate "
                        + "primitive-unimodular classification boundary."))),
            DescribeRole.Theorem))));

    private static Formula RenormalizationFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula length = F.Id("L");
        Formula scale = F.Id("a");
        Formula phi = Varphi;
        Formula inverseScale = new Formula.Power(scale, Seq(Minus, D(1)));
        Formula r = F.Id("R");
        Formula j = F.Id("J");
        Formula reverse = new Formula.Power(r, Seq(Minus, D(1)));
        Formula state = Call("pair", delta, length);
        Formula updated = Call(
            "pair", Multiply(inverseScale, delta), Multiply(scale, length));
        Formula updateLaw = Equal(Call("mulVec", r, state), updated);
        Formula productLaw = Equal(
            Multiply(Multiply(inverseScale, delta), Multiply(scale, length)),
            Multiply(delta, length));
        Formula reflectionLaw = Equal(Multiply(Multiply(j, r), j), reverse);
        Formula inverseLaws = All(
            Equal(Multiply(r, reverse), D(1)),
            Equal(Multiply(reverse, r), D(1)));
        Formula conclusions = All(updateLaw, productLaw, reflectionLaw, inverseLaws);

        return Disp(Seq(
            F.Id("let"), Sp, scale, Sp, Eq, Sp, new Formula.Power(phi, D(2)), Semi, Sp,
            F.Id("let"), Sp, r, Sp, Eq, Sp,
              Call("diag2", inverseScale, scale), Semi, Sp,
            F.Id("let"), Sp, j, Sp, Eq, Sp, Call("matrix2", D(0), D(1), D(1), D(0)),
            Semi, Sp,
            ForAll("delta", real, ForAll("L", real, conclusions))));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
