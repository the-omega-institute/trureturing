using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class BooleanCompanionMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A surjective Boolean effective image has a surjective row or column, and the converse holds.",
        H("Boolean Effective Images Have a Surjective Slice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-effective-image-surjective-slice"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/BooleanCompanionMinimality."
                        + "binary_effective_image_surjective_iff"),
                H("Surjective image iff a row or column is surjective"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonempty source alphabets A and B, let psi:A times B to Bool be a "
                            + "binary companion. Its uncurry map is surjective exactly when at "
                            + "least one fixed row or one fixed column is surjective onto Bool.")),
                    Paragraph(Text(
                        "The forward implication is the Boolean dichotomy used in the one-companion "
                            + "part of the source theorem: if no row is surjective then every row is "
                            + "constant, and two global output witnesses force every column to be "
                            + "surjective. The reverse implication only uses nonemptiness of the "
                            + "other alphabet to lift a row or column witness to the product.")),
                    Paragraph(Text(
                        "This closes the structural effective-image slice clause. The response-width "
                            + "comparison for arbitrary four-endpoint orders and the full two-companion "
                            + "minimality theorem remain open because the available width theorem has "
                            + "a fixed order pattern and a surjective-slice hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Product(Formula left, Formula right) =>
        Call("Prod", left, right);

    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        Seq(Open, LambdaLower, Sp, variable, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula aType = F.Id("A");
        Formula bType = F.Id("B");
        Formula psi = F.Id("psi");
        Formula pair = F.Id("p");
        Formula rowVariable = F.Id("a");
        Formula columnVariable = F.Id("b");
        Formula fixedRow = F.Id("b");
        Formula fixedColumn = F.Id("a");
        Formula boolType = F.Id("Bool");
        Formula first = Call("fst", pair);
        Formula second = Call("snd", pair);
        Formula productMap = Lambda(
            pair,
            Product(aType, bType),
            Apply(psi, first, second));
        Formula rowSurjective = Call(
            "Surjective",
            Lambda(rowVariable, aType, Apply(psi, rowVariable, fixedRow)));
        Formula columnSurjective = Call(
            "Surjective",
            Lambda(columnVariable, bType, Apply(psi, fixedColumn, columnVariable)));
        Formula slices = Seq(
            Open,
            Exists, Sp, fixedRow, Colon, Sp, bType, Comma, Sp, rowSurjective,
            Sp, Lor, Sp,
            Exists, Sp, fixedColumn, Colon, Sp, aType, Comma, Sp, columnSurjective,
            Close);

        return Disp(Seq(
            Forall, Sp, aType, Comma, Sp, bType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Nonempty", aType), Comma, Sp,
            Typeclass("Nonempty", bType), Comma, Sp,
            psi, Colon, Sp, Arrow(aType, Arrow(bType, boolType)), Comma, Sp,
            Call("Surjective", productMap), Sp, Iff, Sp, slices, Dot));
    }
}
