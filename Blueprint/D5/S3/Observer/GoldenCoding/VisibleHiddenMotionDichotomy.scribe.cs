using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class VisibleHiddenMotionDichotomyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy."
            + "visible_path_hidden_address_dichotomy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous solenoid histories remain on visible flow lines, whereas a canonical "
            + "hidden integer action has no continuous real extension.",
        H("Visible Paths and Hidden Address Jumps"),
        Blocks(Describe.Lean(
            DescribeId.Create("visible-path-hidden-address-dichotomy"),
            DeclarationHandle.Create(Declaration),
            H("Continuity is carried by flow lines and hidden changes are rigid"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen path-orbit theorem identifies continuous reachability in the "
                        + "universal solenoid with translation along one real-flow orbit. The "
                        + "frozen hidden-fiber theorem independently makes every continuous "
                        + "hidden-address map on a preconnected real segment constant.")),
                Paragraph(Text(
                    "The same public statement names the canonical additive integer jump. It is "
                        + "nonzero, and frozen continuous rigidity rules out any continuous "
                        + "additive real flow whose restriction along integer casting is that "
                        + "jump. Thus the discrete witness and its obstruction concern one map.")),
                Paragraph(Text(
                    "No new motion, address, path, or flow object is introduced here. Each clause "
                        + "uses the canonical carrier and operation from its frozen owner."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula solenoid = F.Id("UniversalSolenoid");
        Formula hidden = F.Id("HiddenAddress");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula time = F.Id("t");
        Formula segment = F.Id("segment");
        Formula offset = F.Id("offset");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula flow = F.Id("flow");
        Formula jump = F.Id("discreteHiddenJump");

        Formula pathClause = Seq(
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), solenoid), Comma, Sp,
            Call("Joined", x, y), Sp, Iff, Sp,
            Exists, Sp, Typed(time, real), Comma, Sp,
            y, Sp, Eq, Sp, Call("realFlow", time), Sp, Plus, Sp, x);

        Formula hiddenClause = Seq(
            Forall, Sp, Typed(segment, Call("Set", real)), Comma, Sp,
            Call("IsPreconnected", segment), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(offset, Arrow(real, hidden)), Comma, Sp,
            Call("ContinuousOn", offset, segment), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(Seq(first, Comma, Sp, second), real), Comma, Sp,
            first, Sp, InMacro, Sp, segment, Sp, Land, Sp,
            second, Sp, InMacro, Sp, segment, Sp, Rightarrow, Sp,
            Apply(offset, first), Sp, Eq, Sp, Apply(offset, second));

        Formula discreteClause = Seq(
            jump, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Neg, Sp, Exists, Sp,
            Typed(flow, Call("CAddHom", real, hidden)), Comma, Sp,
            flow, Sp, Circ, Sp, F.Id("cast"), Underscore,
            Grp(Mathbb, Grp(F.Id("Z"))), Sp, Eq, Sp, jump);

        return Disp(new Formula.Aligned([
            Seq(Open, pathClause, Close, Sp, Land),
            Seq(Open, hiddenClause, Close, Sp, Land),
            Seq(discreteClause, Dot),
        ]));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
