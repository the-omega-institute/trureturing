using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class GeneralCommutatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fibers/BipartiteBlockade/GeneralCommutator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The double commutator of a legal-flip Hamiltonian on the complete independent-set basis.",
        H("General finite-graph blockade identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("general-double-commutator"),
            DeclarationHandle.Create(Prefix + "general_double_commutator"),
            H("The double commutator splits into blockade and edge exchanges"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The vertices form an arbitrary finite simple graph. The Hilbert-space "
                    + "basis contains every independent vertex subset, including the vacuum. "
                    + "The number projector tests occupation, and the blockade projector tests "
                    + "whether the open neighborhood is empty. Each Hamiltonian transition "
                    + "toggles one legal occupation with its assigned complex drive amplitude.")),
                Paragraph(Text(
                    "At distinct nonadjacent sites, the legal toggles commute and preserve the "
                    + "other occupation projector. On an edge, the two possible flip orders "
                    + "leave exactly the legal exchange between configurations whose symmetric "
                    + "difference is that edge. The same-site term is twice the diagonal "
                    + "combination of twice occupation minus blockade. Summing over sites "
                    + "gives the identity without assumptions of connectivity or bipartiteness.")),
                Paragraph(Text(
                    "This operator identity supplies the algebraic part of two-color recovery. "
                    + "It does not by itself prove a sharp lower bound on the number of drive "
                    + "settings, a dimension statement for density-state fibers, or a claim of "
                    + "literature novelty."))),
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
    private static Formula Formula() => Disp(Seq(
        Forall, Sp, V("V"), Colon, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, C("SimpleGraph", V("V")), Comma, Sp,
        V("Ω"), Colon, Seq(V("V"), Rightarrow, C("Complex")), Comma, Sp,
        V("v"), Colon, V("V"), Comma, Sp,
        C("bracket", C("hamiltonian", V("G"), V("Ω")),
            C("bracket", C("hamiltonian", V("G"), V("Ω")),
                C("number", V("G"), V("v")))),
        Sp, Eq, Sp,
        C("smul", Seq(D(2), V("Ω"), Open, V("v"), Close, Caret, D(2)),
            Seq(C("smul", D(2), C("number", V("G"), V("v"))),
                Minus, C("blockade", V("G"), V("v")))), Plus,
        Seq(new Formula.Subscript(Sum, Seq(V("u"), Colon, Sp, V("V"))), Sp,
            C("ite", C("Adj", V("G"), V("u"), V("v")),
                C("smul", Seq(C("Ω", V("u")), C("Ω", V("v"))),
                    C("exchange", V("G"), V("u"), V("v"))), D(0))), Dot));
}
