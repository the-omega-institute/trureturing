using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class BipartiteTwoColorInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fibers/BipartiteTwoColorInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The P3 exchange identity and the two-color inverse for a blocking readout.",
        H("Bipartite Two-Color Inverse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p3-double-commutator"),
                DeclarationHandle.Create(Prefix + "p3_double_commutator"),
                H("P3 double commutator"),
                StatementSource.FromAuthor(P3Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The five basis configurations are the empty configuration, the three "
                            + "single occupations, and the simultaneous occupation of the two "
                            + "leaves. The displayed Hamiltonian connects configurations that "
                            + "differ by one legal occupation flip.")),
                    Paragraph(Text(
                        "For the central occupation projector, the double commutator splits into "
                            + "a diagonal blocking term and the two exchange operators on the "
                            + "edges incident to the center. The identity is checked entry by "
                            + "entry over the finite five-state basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-color-inverse-a"),
                DeclarationHandle.Create(Prefix + "two_color_inverse_A"),
                H("A-color scaling recovers the blocking coordinate"),
                StatementSource.FromAuthor(InverseAFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the unscaled and A-color-scaled accelerations have the displayed "
                        + "diagonal and exchange contributions, their difference cancels the "
                        + "exchange term and isolates the blocking coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-color-inverse-b"),
                DeclarationHandle.Create(Prefix + "two_color_inverse_B"),
                H("B-color scaling recovers the blocking coordinate"),
                StatementSource.FromAuthor(InverseBFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the central B-color drive is unchanged while its neighboring A-color "
                        + "drives are doubled, the second linear combination cancels exchange "
                        + "contributions and recovers the same blocking coordinate."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula V(string name) => F.Id(name);

    private static Formula P3Formula() => Disp(Seq(
        Forall, Sp, V("Ωu"), Comma, Sp, V("Ωv"), Comma, Sp, V("Ωw"), Comma, Sp,
        C("doubleCommutator", C("p3Hamiltonian", V("Ωu"), V("Ωv"), V("Ωw")),
            C("occupationV")), Sp, Eq, Sp,
        Seq(C("smul", Seq(D(2), V("Ωv"), Caret, D(2)),
            Seq(D(2), C("occupationV"), Minus, C("blockingV"))),
            Plus, C("smul", Seq(V("Ωu"), V("Ωv")), C("exchangeUV")),
            Plus, C("smul", Seq(V("Ωv"), V("Ωw")), C("exchangeVW"))), Dot));

    private static Formula InverseAFormula() => Disp(Seq(
        Forall, Sp, V("m"), Comma, Sp, V("b"), Comma, Sp, V("a"), Comma, Sp,
        V("aPrime"), Comma, Sp, V("Ω"), Comma, Sp,
        V("a"), Sp, Eq, Sp, Seq(Minus, Seq(Open, Seq(D(2), V("Ω"), Caret, D(2),
            Seq(Open, D(2), V("m"), Minus, V("b"), Close)), Plus, D(1), Close)),
        Comma, Sp, V("aPrime"), Sp, Eq, Sp, Seq(Minus, Seq(Open, Seq(D(8), V("Ω"), Caret, D(2),
            Seq(Open, D(2), V("m"), Minus, V("b"), Close)), Plus, D(2), Close)),
        Comma, Sp, V("Ω"), Sp, Neq, Sp, D(0), Rightarrow, Sp,
        V("b"), Sp, Eq, Sp, Seq(D(2), V("m"), Plus,
            new Formula.Fraction(Seq(Open, V("aPrime"), Minus, D(2), V("a"), Close),
                Seq(D(4), V("Ω"), Caret, D(2)))), Dot));

    private static Formula InverseBFormula() => Disp(Seq(
        Forall, Sp, V("m"), Comma, Sp, V("b"), Comma, Sp, V("a"), Comma, Sp,
        V("aPrime"), Comma, Sp, V("Ω"), Comma, Sp,
        V("a"), Sp, Eq, Sp, Seq(Minus, Seq(Open, Seq(D(2), V("Ω"), Caret, D(2),
            Seq(Open, D(2), V("m"), Minus, V("b"), Close)), Plus, D(1), Close)),
        Comma, Sp, V("aPrime"), Sp, Eq, Sp, Seq(Minus, Seq(Open, Seq(D(2), V("Ω"), Caret, D(2),
            Seq(Open, D(2), V("m"), Minus, V("b"), Close)), Plus, D(2), Close)),
        Comma, Sp, V("Ω"), Sp, Neq, Sp, D(0), Rightarrow, Sp,
        V("b"), Sp, Eq, Sp, Seq(D(2), V("m"), Plus,
            new Formula.Fraction(Seq(Open, D(2), V("a"), Minus, V("aPrime"), Close),
                Seq(D(2), V("Ω"), Caret, D(2)))), Dot));
}
