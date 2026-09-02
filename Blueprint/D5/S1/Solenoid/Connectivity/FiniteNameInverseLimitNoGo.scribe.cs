using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid.Connectivity;

internal sealed class FiniteNameInverseLimitNoGoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous finite-name inverse-limit readings of a connected space are constant.",
        H("Finite-Name Inverse-Limit No-Go"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-name-inverse-limit-no-go"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo."
                        + "finite_name_inverse_limit_no_go"),
                H("A finite-name inverse limit cannot distinguish a connected space"),
                StatementSource.FromAuthor(NoGoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let finiteNames be a sequential diagram of finite sets, each carrying "
                            + "its discrete topology, and let name map a connected space X "
                            + "continuously into the canonical profinite limit of that diagram.")),
                    Paragraph(Text(
                        "Every two values of name coincide. Consequently its range is exactly "
                            + "the singleton containing the value at any chosen point of X; if "
                            + "name is also injective, X itself is a subsingleton.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the canonical profinite limit cone and the exact "
                            + "theorem that a continuous map from a connected space to a totally "
                            + "disconnected space is constant. Repository search found only "
                            + "single-discrete-target and particular-product specializations."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula NoGoFormula()
    {
        Formula xType = F.Id("X");
        Formula finiteNames = F.Id("finiteNames");
        Formula name = F.Id("name");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula xZero = F.Id("x0");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula categoryOpposite = Call("Opposite", naturalNumbers);
        Formula finiteCategory = F.Id("FintypeCat");
        Formula profiniteDiagram = Call("toProfinite", finiteNames);
        Formula limit = Call("ProfiniteLimit", profiniteDiagram);
        Formula constantClause = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            Call("name", x), Sp, Eq, Sp, Call("name", y));
        Formula singletonImageClause = Seq(
            Forall, Sp, xZero, Colon, Sp, xType, Comma, Sp,
            Call("range", name), Sp, Eq, Sp,
            OpenBrace, Call("name", xZero), CloseBrace);
        Formula injectiveClause = Seq(
            Call("Injective", name), Sp, Rightarrow, Sp, Call("Subsingleton", xType));

        return Disp(Seq(
            Forall, Sp, xType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("TopologicalSpace", xType), CloseBracket, Comma, Sp,
            OpenBracket, Call("ConnectedSpace", xType), CloseBracket, Comma, Esc,
            finiteNames, Colon, Sp, Call("Functor", categoryOpposite, finiteCategory), Comma, Esc,
            name, Colon, Sp, new Formula.TypeArrow(xType, limit), Comma, Sp,
            Call("Continuous", name), Sp, Rightarrow, RowBreak,
            Grp(constantClause), Sp, Land, RowBreak,
            Grp(singletonImageClause), Sp, Land, RowBreak,
            Grp(injectiveClause), Dot));
    }
}
