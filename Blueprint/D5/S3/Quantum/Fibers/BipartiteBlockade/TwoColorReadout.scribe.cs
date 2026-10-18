using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class TwoColorReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matrix accelerations recover empty-neighborhood means under two positive color-scaled drives.",
        H("Two-color blockade readout"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-color-readout-inverse"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/TwoColorReadout.two_color_readout_inverse"),
            H("Exact inverse from two actual accelerations"),
            StatementSource.FromAuthor(Inverse()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Choose a proper Boolean coloring of a finite simple graph. The true color "
                    + "is the class whose drives are doubled. Every edge joins opposite colors, "
                    + "so every exchange coefficient doubles. The local diagonal coefficient "
                    + "quadruples on the true color and remains fixed on the false color.")),
                Paragraph(Text(
                    "Occupation and blockade means are the real parts of matrix trace pairings. "
                    + "Acceleration is minus the real trace pairing with the actual nested "
                    + "Hamiltonian commutator. The two scaling equations follow from the "
                    + "finite-graph operator identity; they are not hypotheses of the inverse.")),
                Paragraph(Text(
                    "The statement applies to every complex matrix and therefore to every "
                    + "positive semidefinite trace-one density matrix. It requires a nonzero "
                    + "drive at the recovered site. Positive drives retain positivity under "
                    + "the color scaling. Both experiments refer to the same matrix state. "
                    + "The inverse follows algebraically from the general identity. Sharp lower "
                    + "bounds additionally require actual indistinguishable density matrices."))),
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
    private static Formula Inverse() => Disp(Seq(
        Forall, Sp, V("V"), Colon, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, C("SimpleGraph", V("V")), Comma, Sp,
        V("c"), Colon, Seq(V("V"), Rightarrow, C("Bool")), Comma, Sp,
        Seq(Open, Forall, Sp, V("u"), Colon, V("V"), Comma, Sp,
            V("w"), Colon, V("V"), Comma, Sp,
            C("Adj", V("G"), V("u"), V("w")), Rightarrow, Sp,
            C("c", V("u")), Sp, Neq, Sp, C("c", V("w")), Close), Comma, Sp,
        V("Ω"), Colon, Seq(V("V"), Rightarrow, C("Real")), Comma, Sp,
        V("ρ"), Colon, C("Matrix", C("Configuration", V("G")), C("Configuration", V("G")), C("Complex")), Comma, Sp,
        V("v"), Colon, V("V"), Comma, Sp,
        C("Ω", V("v")), Sp, Neq, Sp, D(0), Rightarrow, Sp,
        C("blockadeMean", V("G"), V("ρ"), V("v")), Sp, Eq, Sp,
        D(2), C("occupationMean", V("G"), V("ρ"), V("v")), Plus,
        C("ite", Seq(C("c", V("v")), Sp, Eq, Sp, C("true")),
            new Formula.Fraction(
                Seq(C("acceleration", V("G"), C("colorScaledDrive", V("c"), V("Ω")), V("ρ"), V("v")),
                    Minus, D(2), C("acceleration", V("G"), V("Ω"), V("ρ"), V("v"))),
                Seq(D(4), C("Ω", V("v")), Caret, D(2))),
            new Formula.Fraction(
                Seq(D(2), C("acceleration", V("G"), V("Ω"), V("ρ"), V("v")),
                    Minus, C("acceleration", V("G"), C("colorScaledDrive", V("c"), V("Ω")), V("ρ"), V("v"))),
                Seq(D(2), C("Ω", V("v")), Caret, D(2)))), Dot));
}
