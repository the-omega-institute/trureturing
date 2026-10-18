using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class SettingNumberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal number of positive drive settings is zero, one or two according to the number of distinct nonlinear neighborhoods.",
        H("Sharp setting number for connected bipartite blockade networks"),
        Blocks(Describe.Lean(
            DescribeId.Create("setting-number-classification"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/SettingNumber.setting_number_classification"),
            H("The minimum positive-drive count"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite connected simple graph with a proper Boolean coloring, d is the "
                    + "number of distinct open neighborhoods having at least two vertices. A count k "
                    + "is feasible when there exist k predetermined strictly positive real vertex "
                    + "drives such that any two complex positive semidefinite trace-one matrices "
                    + "with equal occupation means and equal accelerations at all k drives have "
                    + "equal blockade means. The setting number is the infimum of these natural "
                    + "counts. The theorem proves this set nonempty and identifies its minimum.")),
                Paragraph(Text(
                    "When d is zero, each blockade is I or I minus one occupation operator. "
                    + "When d is one, the signed color sum of one acceleration readout recovers "
                    + "the sole nonlinear class. Two settings always suffice: start with unit "
                    + "drive and double precisely one color. The actual commutator identity "
                    + "then supplies the two-color inverse.")),
                Paragraph(Text(
                    "For the lower bounds, a degree-two-or-larger neighborhood admits two actual "
                    + "density matrices with equal occupations and unequal blockade. If there are "
                    + "two distinct nonlinear neighborhoods, every positive drive admits two actual "
                    + "density matrices with equal occupations and accelerations yet an unequal "
                    + "blockade. The latter states include compensating coherences. These "
                    + "existence statements quantify over the same graph and the prescribed drive; "
                    + "counting unknowns alone does not supply the lower bound.")),
                Paragraph(Text(
                    "The contract uses initial occupation means and second-order accelerations. "
                    + "It assumes repeated preparation of the same unknown state. It makes no "
                    + "claim about higher derivatives, full trajectories, finite-sample estimates "
                    + "or a time-derivative bridge beyond the nested-commutator definition."))),
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
        C("Connected", V("G")), Rightarrow,
        Forall, Sp, V("c"), Colon, Seq(V("V"), Rightarrow, C("Bool")), Comma,
        Open, Forall, Sp, V("u"), Comma, V("v"), Colon, V("V"), Comma,
        C("Adj", V("G"), V("u"), V("v")), Rightarrow,
        C("c", V("u")), Neq, C("c", V("v")), Close, Rightarrow,
        C("Nonempty", C("feasibleSettingCounts", V("G"))), Land,
        C("settingNumber", V("G")), Eq,
        C("min", D(2), C("card", C("nonlinearNeighborhoods", V("G")))), Dot));
}
