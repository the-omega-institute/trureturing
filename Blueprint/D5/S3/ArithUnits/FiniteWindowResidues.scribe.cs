using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class FiniteWindowResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite coprime residue window has a bounded simultaneous representative.",
        H("Finite-Window Residue Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-pairwise-coprime-residue-windows-are-realizable"),
                DeclarationHandle.Create("D5/S3/ArithUnits/FiniteWindowResidues.finite_window_residues_realizable"),
                H("Every finite pairwise-coprime residue window is realizable"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("W"), Comma, F.Id("a"), Comma, F.Id("m"), Comma, Esc,
                                    Operatorname, Grp(F.Id("pairwiseCoprime")),
                                    Open, F.Id("m"), Comma, F.Id("W"), Close, Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("W"), Comma, Esc,
                                    F.Id("m"), Underscore, F.Id("i"), Sp, Neq, Sp, D(0), Close,
                                    Sp, Rightarrow, Sp, Exists, Sp, F.Id("n"), Lt,
                                    Prod, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("W")),
                                    F.Id("m"), Underscore, F.Id("i"), Comma, Esc,
                                    Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("W"), Comma, Esc,
                                    F.Id("n"), Sp, Equiv, Sp, F.Id("a"), Underscore, F.Id("i"), Esc,
                                    Open, Operatorname, Grp(F.Id("mod")), Esc,
                                    F.Id("m"), Underscore, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Fix a finite window of indices, a nonzero modulus at each index, "
                                        + "and an arbitrary target residue at each index. When the window's "
                                        + "moduli are pairwise coprime, one natural number realizes every "
                                        + "target congruence simultaneously. The witness is bounded strictly "
                                        + "below the product of the moduli, making the finite period explicit "
                                        + "rather than asserting only an unbounded existence claim.")),
                                    Paragraph(Text(
                                        "The library was searched before proving. Pinned Mathlib supplies the "
                                        + "simultaneous witness as Nat.chineseRemainderOfFinset and proves its "
                                        + "product bound as Nat.chineseRemainderOfFinset_lt_prod. The Lean "
                                        + "declaration is therefore a thin honest wrapper that packages those "
                                        + "two facts into the source atom's finite-window realization form. "
                                        + "The source's concrete residue scan is treated as an illustrative "
                                        + "certificate and is not promoted into the universal theorem."))),
                DescribeRole.Theorem
            ))));
}
