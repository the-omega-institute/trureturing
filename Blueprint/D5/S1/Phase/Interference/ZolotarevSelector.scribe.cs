using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class ZolotarevSelectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The inverse-residue congruence factors the selector Jacobi symbol.",
        H("Zolotarev Selector Congruence"),
        Blocks(
            Describe.Lean(DescribeId.Create("zolotarev-selector-congruence"),
                DeclarationHandle.Create(
                                    "D5/S1/Phase/Interference/ZolotarevSelector."
                                    + "zolotarev_selector_congruence"),
                H("The inverse-residue congruence factors the selector symbol"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("b"), Comma, Sp, F.Id("g"), Comma, Sp,
                                    F.Id("d"), Colon, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                                    D(4), F.Id("b"), F.Id("g"), Sp, Equiv, Sp, Minus, D(1),
                                    Sp, Open, Operatorname, Grp(F.Id("mod")), Sp, F.Id("d"), Close,
                                    Sp, Rightarrow, Esc,
                                    Open, Frac, Grp(D(2), F.Id("g")), Grp(Lvert, Sp, F.Id("d"), Sp, Rvert), Close,
                                    Eq,
                                    Open, Frac, Grp(D(2)), Grp(Lvert, Sp, F.Id("d"), Sp, Rvert), Close,
                                    Open, Frac, Grp(Minus, D(1)), Grp(Lvert, Sp, F.Id("d"), Sp, Rvert), Close,
                                    Open, Frac, Grp(F.Id("b")), Grp(Lvert, Sp, F.Id("d"), Sp, Rvert), Close,
                                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The Zolotarev inverse-residue congruence 4bg = -1 modulo d makes 2g "
                                        + "and -2b inverse residues, so their Jacobi symbols agree and the "
                                        + "selector symbol at 2g factors into the three displayed Jacobi "
                                        + "symbols over the absolute modulus. The factorization side reuses "
                                        + "the frozen selector-numerator theorem; the transport side carries "
                                        + "the congruence through the natural-absolute-value reduction.")),
                                    Paragraph(Text(
                                        "An explicit witness at b = g = 1, d = 5 exercises the congruence "
                                        + "with a nontrivial value of the two-symbol, so the statement is not "
                                        + "vacuously satisfied."))),
                DescribeRole.Theorem))));
}
