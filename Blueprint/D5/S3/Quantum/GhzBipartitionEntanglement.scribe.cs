using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class GhzBipartitionEntanglementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty bipartition of the finite GHZ state has rank two and entropy log two.",
        H("GHZ Entanglement Across Every Nontrivial Cut"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ghz-entangled-across-every-nontrivial-cut"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/GhzBipartitionEntanglement."
                        + "ghz_entangled_across_every_nontrivial_cut"),
                H("Every nontrivial GHZ cut has two equal Schmidt weights"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two sides of the cut are arbitrary nonempty types. Their all-zero "
                            + "and all-one configurations are therefore distinct, and the GHZ "
                            + "amplitude is supported exactly on the two matching global constant "
                            + "configurations.")),
                    Paragraph(Text(
                        "The logical coefficient matrix is diagonal with entries inverse square "
                            + "root of two. The proof checks its norm directly and uses the "
                            + "nonzero determinant criterion to obtain matrix rank two.")),
                    Paragraph(Text(
                        "Multiplying by its conjugate transpose gives one half of the identity. "
                            + "Thus both displayed reduced weights are one half, and direct "
                            + "evaluation of their entropy gives log two. The construction is "
                            + "mathematical and does not assert that zeta data supplies a physical "
                            + "quantum state."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula left = F.Id("A");
        Formula right = F.Id("B");
        Formula coefficient = Seq(F.Id("C"), Underscore, Grp(F.Id("GHZ")));
        Formula reduced = Rho;
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula identity = Seq(F.Id("I"), Underscore, Grp(D(2)));
        Formula entropy = Seq(F.Id("S"), Underscore, Grp(left));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            left, Sp, Neq, Sp, Emptyset, Comma, Sp,
            right, Sp, Neq, Sp, Emptyset, Sp, Rightarrow, RowBreak, Grp(),
            Call("rank", coefficient), Sp, Eq, Sp, D(2), Sp, Land, RowBreak, Grp(),
            reduced, Sp, Eq, Sp, half, Sp, identity, Sp, Land, RowBreak, Grp(),
            Forall, Sp, F.Id("i"), Sp, InMacro, Sp, OpenBrace, D(0), Comma, D(1), CloseBrace,
            Comma, Sp, reduced, Underscore, Grp(F.Id("ii")), Sp, Eq, Sp, half,
            Sp, Land, RowBreak, Grp(),
            entropy, Sp, Eq, Sp, Log, Sp, D(2), Dot,
            End, Grp(F.Id("gathered"))));
    }

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
}
