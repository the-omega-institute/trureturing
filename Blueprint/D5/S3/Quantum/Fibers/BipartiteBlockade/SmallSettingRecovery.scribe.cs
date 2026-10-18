using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class SmallSettingRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Means alone recover linear neighborhood blockades; one nonzero drive recovers a single nonlinear neighborhood class.",
        H("Recovery with zero or one nonlinear neighborhood"),
        Blocks(Describe.Lean(
            DescribeId.Create("small-setting-recovery"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/SmallSettingRecovery.small_setting_recovery"),
            H("Exact small-setting recovery"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite simple graph with a proper Boolean coloring and a real drive "
                    + "that is nonzero at every vertex. Let d count distinct open neighborhoods "
                    + "containing at least two vertices. Matrices have equal real trace. "
                    + "If d is zero, equality of every occupation mean implies equality of every "
                    + "blockade mean. If d is at most one, equality of occupations and accelerations "
                    + "under this one drive implies equality of blockades.")),
                Paragraph(Text(
                    "An empty neighborhood has blockade operator I. A singleton neighborhood {u} "
                    + "has blockade I minus the occupation operator at u. For larger neighborhoods, "
                    + "sum the acceleration equations with the signs of the two colors. Edge "
                    + "exchange contributions cancel in pairs. All vertices sharing a nonempty "
                    + "neighborhood have the same color, so a unique nonlinear class has a nonzero "
                    + "signed coefficient. The surviving scalar equation determines its blockade.")),
                Paragraph(Text(
                    "The hypotheses do not require positivity or Hermiticity of either matrix. "
                    + "Equal trace holds for trace-one density matrices. Connectivity is unnecessary "
                    + "for these upper bounds. Acceleration means the actual nested commutator "
                    + "trace at the prescribed drive."))),
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
    private static Formula PairRecovery(bool acceleration) => Seq(
        Forall, Sp, V("ρ"), Comma, Sp, V("σ"), Colon,
        C("Matrix", C("Configuration", V("G")), C("Configuration", V("G")), C("Complex")), Comma, Sp,
        C("ReTrace", V("ρ")), Eq, C("ReTrace", V("σ")), Rightarrow,
        Open, Forall, Sp, V("v"), Colon, V("V"), Comma,
        C("occupationMean", V("G"), V("ρ"), V("v")), Eq,
        C("occupationMean", V("G"), V("σ"), V("v")), Close, Rightarrow,
        acceleration ? Seq(Open, Forall, Sp, V("v"), Colon, V("V"), Comma,
            C("acceleration", V("G"), V("Ω"), V("ρ"), V("v")), Eq,
            C("acceleration", V("G"), V("Ω"), V("σ"), V("v")), Close, Rightarrow) : Seq(),
        Forall, Sp, V("v"), Colon, V("V"), Comma,
        C("blockadeMean", V("G"), V("ρ"), V("v")), Eq,
        C("blockadeMean", V("G"), V("σ"), V("v")));
    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, C("Type"), Comma,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma,
        V("G"), Colon, C("SimpleGraph", V("V")), Comma,
        V("c"), Colon, Seq(V("V"), Rightarrow, C("Bool")), Comma,
        Open, Forall, Sp, V("u"), Comma, V("v"), Colon, V("V"), Comma,
        C("Adj", V("G"), V("u"), V("v")), Rightarrow,
        C("c", V("u")), Neq, C("c", V("v")), Close, Rightarrow,
        Forall, Sp, V("Ω"), Colon, Seq(V("V"), Rightarrow, C("Real")), Comma,
        Open, Forall, Sp, V("v"), Colon, V("V"), Comma, C("Ω", V("v")), Neq, D(0), Close,
        Rightarrow,
        Open, C("nonlinearNeighborhoods", V("G")), Eq, C("empty"), Rightarrow,
        PairRecovery(false), Close, Land,
        Open, C("card", C("nonlinearNeighborhoods", V("G"))), Le, D(1), Rightarrow,
        PairRecovery(true), Close, Dot));
}
