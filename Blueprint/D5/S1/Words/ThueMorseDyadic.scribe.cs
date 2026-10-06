using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ThueMorseDyadicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ThueMorseDyadic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/joshirust2025monochromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared binary block identities for the actual Thue-Morse word.",
        H("Dyadic Thue-Morse Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thue-morse-dyadic-block"),
                DeclarationHandle.Create(Prefix + "dyadic_block"),
                H("Parity splits at a dyadic boundary"),
                StatementSource.FromAuthor(Disp(BlockFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "This is the general binary block proof extracted from the existing "
                    + "ThueMorseMapFirstStart result. The binary recursion proves it by "
                    + "induction on e, splitting the residue into even and odd cases. "
                    + "Both ThueMorseMapFirstStart.result and ThueMorseMapInfiniteFibers.result "
                    + "consume this shared supplier on their live proof paths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thue-morse-top-parity"),
                DeclarationHandle.Create(Prefix + "top_parity"),
                H("The all-one block has its length's parity"),
                StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll, "e",
                    Equal(Call("t", Subtract(new Formula.Power(D(2), F.Id("e")), D(1))),
                        Call("oddBit", F.Id("e")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The existing top parity proof is extracted without changing its "
                    + "statement. Adding one leading binary digit negates the color, "
                    + "so t(2^e-1)=oddBit(e), where oddBit is the Boolean test "
                    + "e mod 2=1. The old first-start "
                    + "proof and the new triple construction both use this theorem."))),
                DescribeRole.Theorem))));

    private static Formula BlockFormula()
    {
        var e = F.Id("e"); var a = F.Id("a"); var r = F.Id("r");
        var power = new Formula.Power(D(2), e);
        return Bind(FormulaQuantifier.ForAll, "e", Bind(FormulaQuantifier.ForAll, "a",
            Bind(FormulaQuantifier.ForAll, "r", Implies(Less(r, power),
                Equal(Call("t", Add(Multiply(a, power), r)), Call("xor", Call("t", a), Call("t", r)))))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
