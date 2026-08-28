using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class LocalLawGluingObstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction."
            + "compatible_local_laws_can_lack_global_state";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise compatible local laws need not admit a joint global state.",
        H("Local-Law Gluing Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-law-gluing-obstruction"),
                DeclarationHandle.Create(Declaration),
                H("Compatible local laws can lack a global realization"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the Boolean pair carrier, E is the equality law and N is the "
                            + "inequality law. Each relevant coordinate projection is the full "
                            + "Boolean carrier, so the three local laws agree on their overlaps.")),
                    Paragraph(Text(
                        "A global triple would force its first two and last two coordinates "
                            + "to agree while forcing its outer coordinates to differ. The same "
                            + "constructed local laws therefore witness the gluing obstruction."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula pairType = Seq(boolean, Sp, Times, Sp, boolean);
        Formula equalLaw = F.Id("E");
        Formula unequalLaw = F.Id("N");
        Formula left = F.Id("u");
        Formula right = F.Id("v");
        Formula first = F.Id("a");
        Formula middle = F.Id("b");
        Formula last = F.Id("c");
        Formula pair = Seq(Open, left, Comma, Sp, right, Close);
        Formula EqualPair(Formula x, Formula y) =>
            Seq(Open, x, Comma, Sp, y, Close);
        Formula LawDefinition(Formula predicate) => Seq(
            OpenBrace, pair, Colon, Sp, pairType, Sp, Mid, Sp,
            predicate, CloseBrace);
        Formula Image(string projection, Formula law) =>
            Call("image", F.Id(projection), law);

        Formula equalDefinition = LawDefinition(Seq(left, Sp, Eq, Sp, right));
        Formula unequalDefinition = LawDefinition(Seq(left, Sp, Neq, Sp, right));
        Formula overlapCompatibility = Seq(
            Image("snd", equalLaw), Sp, Eq, Sp, Image("fst", equalLaw), Sp,
            Land, RowBreak, Grp(),
            Image("fst", equalLaw), Sp, Eq, Sp, Image("fst", unequalLaw), Sp,
            Land, RowBreak, Grp(),
            Image("snd", equalLaw), Sp, Eq, Sp, Image("snd", unequalLaw));
        Formula noGlobalState = Seq(
            Neg, Exists, Sp,
            first, Comma, Sp, middle, Comma, Sp, last,
            Colon, Sp, boolean, Comma, RowBreak, Grp(),
            EqualPair(first, middle), Sp, InMacro, Sp, equalLaw, Sp, Land, Sp,
            EqualPair(middle, last), Sp, InMacro, Sp, equalLaw, Sp, Land,
            RowBreak, Grp(),
            EqualPair(first, last), Sp, InMacro, Sp, unequalLaw);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("let")), Sp,
            equalLaw, Colon, Sp, Call("Set", pairType), Sp, Colon, Eq, Sp,
            equalDefinition, Comma, RowBreak, Grp(),
            unequalLaw, Colon, Sp, Call("Set", pairType), Sp, Colon, Eq, Sp,
            unequalDefinition, SemiSpace, RowBreak, Grp(),
            Open, overlapCompatibility, Close, Sp, Land, RowBreak, Grp(),
            Open, noGlobalState, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
