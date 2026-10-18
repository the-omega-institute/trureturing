using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class FiveModeSettingNumberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For maximum degree two, exactly the same positive drives identify all blockade probabilities and all five-mode Born marginals.",
        H("The sharp five-mode recovery count"),
        Blocks(Describe.Lean(
            DescribeId.Create("five-mode-setting-number-classification"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/FiveModeSettingNumber.five_mode_setting_number_classification"),
            H("Equality of feasible settings and their minimum"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite connected simple graph with a proper Boolean coloring and "
                    + "at most two neighbors at every vertex. A five-mode setting collection is "
                    + "sufficient when every two complex positive semidefinite trace-one states "
                    + "with the same initial occupations and prescribed-drive accelerations have "
                    + "the same complete Born law at each degree-two center. Endpoint order is "
                    + "explicit; the five modes are vacuum, left, center, right and both ends.")),
                Paragraph(Text(
                    "For a degree-two center v with endpoints u and w, write b for its blockade "
                    + "mean. The five masses are b minus m_v, 1 minus b minus m_w, m_v, "
                    + "1 minus b minus m_u, and b minus 1 plus m_u plus m_w. Thus equal "
                    + "occupations and blockades determine the entire law. Conversely its "
                    + "vacuum and center masses sum to b. Degree-zero and degree-one blockades "
                    + "already follow from the trace and occupations. These relations prove "
                    + "equality of the two data contracts for each fixed drive collection.")),
                Paragraph(Text(
                    "Both feasible-count sets require every drive to be strictly positive and "
                    + "chosen in advance. Their equality transfers the actual-density lower bounds "
                    + "and the explicit zero-, one- and two-setting upper bounds. The common "
                    + "minimum is the number of distinct nonlinear neighborhoods capped at two. "
                    + "All local laws come from the diagonal Born marginal of the same global state; "
                    + "no independent local-state assumption is introduced."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, C("Type"), Comma,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma,
        V("G"), Colon, C("SimpleGraph", V("V")), Comma,
        C("Connected", V("G")), Rightarrow, Sp,
        Forall, Sp, V("c"), Colon, Seq(V("V"), Rightarrow, Sp, C("Bool")), Comma,
        Open, Forall, Sp, V("u"), Comma, V("v"), Colon, V("V"), Comma,
        C("Adj", V("G"), V("u"), V("v")), Rightarrow, Sp,
        C("c", V("u")), Neq, Sp, C("c", V("v")), Close, Rightarrow, Sp,
        Open, Forall, Sp, V("v"), Colon, V("V"), Comma,
        C("card", C("neighborFinset", V("G"), V("v"))), Le, Sp, D(2), Close, Rightarrow, Sp,
        C("feasibleFiveModeCounts", V("G")), Eq, Sp, C("feasibleSettingCounts", V("G")), Land, Sp,
        C("Nonempty", C("feasibleFiveModeCounts", V("G"))), Land, Sp,
        C("fiveModeSettingNumber", V("G")), Eq, Sp,
        C("min", D(2), C("card", C("nonlinearNeighborhoods", V("G")))), Dot));
}
