using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Nested golden return maps have an exact all-resolution carry correction. "
                + "Their commutator is independent of the nonzero input.",
            H("Golden Clock Composition and Order Defect"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-clock-composition"),
                    DeclarationHandle.Create(Prefix + "entry_compose"),
                    H("Exact composition of nested return maps"),
                    StatementSource.FromAuthor(CompositionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For all natural K,L and all nonzero integer m, let "
                                + "T(L,m)=F(L+3)*m+F(L+2)*floor(m*alpha). Then "
                                + "T(K,T(L,m))=T(K+L+2,m)-F(K+2)*cutCarry(L). "
                                + "cutCarry is zero for a positive signed window and one "
                                + "for a negative signed window. It starts at zero and "
                                + "flips at every resolution step.")),
                        Paragraph(Text(
                            "lattice_composition first composes both integer coordinates. "
                                + "floor_entry then proves the exact one-unit correction "
                                + "lost when only the visible integer coordinate is retained. "
                                + "Neither the composition law nor the carry law is supplied "
                                + "as a structure field or a theorem assumption."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-clock-commutator"),
                    DeclarationHandle.Create(Prefix + "entry_commutator"),
                    H("Changing composition order has an explicit arithmetic defect"),
                    StatementSource.FromAuthor(CommutatorFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The defect is F(L+2)*cutCarry(K)-F(K+2)*cutCarry(L). "
                                + "entry_commute_iff turns vanishing of this finite "
                                + "arithmetic expression into the exact commutation "
                                + "criterion, uniformly over every nonzero input m.")),
                        Paragraph(Text(
                            "This is a statement about nested arithmetic return maps. "
                                + "It is not a claim that ordinary circle rotations fail "
                                + "to commute, and it does not identify a depth increment "
                                + "with a physical time step."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CompositionFormula() => Disp(Seq(
        Call("entry", F.Id("K"), Call("entry", F.Id("L"), F.Id("m"))),
        Sp, Eq, Sp,
        Call("sub",
            Call("entry", Seq(F.Id("K"), Plus, F.Id("L"), Plus, F.Id("2")), F.Id("m")),
            Seq(Call("boundary", F.Id("K")), Cdot, Call("cutCarry", F.Id("L"))))));

    private static Formula CommutatorFormula() => Disp(Seq(
        Call("commutator", F.Id("K"), F.Id("L"), F.Id("m")), Sp, Eq, Sp,
        Call("sub",
            Seq(Call("boundary", F.Id("L")), Cdot, Call("cutCarry", F.Id("K"))),
            Seq(Call("boundary", F.Id("K")), Cdot, Call("cutCarry", F.Id("L"))))));
}
