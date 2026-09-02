using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HilbertGeometry;

internal sealed class GoldenAntiIsometryDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/HilbertGeometry/GoldenAntiIsometry.golden_anti_isometry";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fibonacci phase update negates the golden quadratic form in every real Hilbert dimension.",
        H("Dimension-Independent Golden Anti-Isometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("dimension-independent-golden-anti-isometry"),
            DeclarationHandle.Create(Declaration),
            H("The Hilbert-space Fibonacci update negates the form"),
            StatementSource.FromAuthor(AntiIsometryFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H be a real Hilbert space and V=H x H. The quadratic form is "
                        + "Q(X,Y)=norm(X)^2-inner(X,Y)-norm(Y)^2, and the linear update is "
                        + "F(X,Y)=(X+Y,X).")),
                Paragraph(Text(
                    "The public conclusion is the single anti-isometry identity "
                        + "Q(F(X,Y))=-Q(X,Y)."))),
            DescribeRole.Theorem))));

    private static Formula AntiIsometryFormula()
    {
        Formula real = F.Id("Real");
        Formula space = F.Id("H");
        Formula phase = Call("Product", space, space);
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula q = F.Id("Q");
        Formula update = F.Id("F");
        Formula qDefinition = Subtract(
            Subtract(Call("normSq", x), Call("inner", x, y)),
            Call("normSq", y));
        Formula updateDefinition = Call("pair", Add(x, y), x);
        Formula conclusion = Equal(
            Apply(q, Apply(update, Call("pair", x, y))),
            Neg(Apply(q, Call("pair", x, y))));

        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, Call("Type"), Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", real, space), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", space), CloseBracket, Comma,
            RowBreak, Grp(),
            F.Id("let"), Sp, F.Id("V"), Sp, Eq, Sp, phase, Semi, Sp,
            F.Id("let"), Sp, q, Open, x, Comma, Sp, y, Close, Sp, Eq, Sp,
            qDefinition, Semi, Sp,
            F.Id("let"), Sp, update, Open, x, Comma, Sp, y, Close, Sp, Eq, Sp,
            updateDefinition, Semi,
            RowBreak, Grp(),
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, space, Comma, Sp,
            conclusion, Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Neg(Formula value) => Seq(Minus, value);
}
