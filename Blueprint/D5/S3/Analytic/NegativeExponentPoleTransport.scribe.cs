using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NegativeExponentPoleTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative dictionary exponent transports a positive-order zero into an exact pole debt.",
        H("Negative-Exponent Pole Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-exponents-transport-zeros-to-pole-debts"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/NegativeExponentPoleTransport."
                    + "negative_exponent_pole_transport"),
                H("Negative exponents transport zeros to pole debts"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("ord")), Underscore,
                    Grp(F.Id("s"), Underscore, D(0)),
                    Open, Prod, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("S")),
                    F.Id("f"), Underscore, F.Id("i"), Caret, Grp(F.Id("e"), Underscore,
                    F.Id("i")), Close, Eq,
                    F.Id("e"), Underscore, F.Id("d"), Sp, F.Id("m"), Plus,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("S"),
                    Setminus, Grp(F.Id("d"))),
                    F.Id("e"), Underscore, F.Id("i"), Sp,
                    Operatorname, Grp(F.Id("ord")), Underscore,
                    Grp(F.Id("s"), Underscore, D(0)),
                    Open, F.Id("f"), Underscore, F.Id("i"), Close,
                    Comma, Quad, Sp,
                    Neg, Sp, Operatorname, Grp(F.Id("Pole")),
                    Open, F.Id("s"), Underscore, D(0), Close,
                    Iff, Sp, D(0), Leq, Sp,
                    Operatorname, Grp(F.Id("ord")), Underscore,
                    Grp(F.Id("s"), Underscore, D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of complex meromorphic factors carry integer "
                        + "exponents. If a distinguished factor has positive local order m "
                        + "and its exponent e_d is negative, then its contribution e_d m is "
                        + "strictly negative. The order of the whole product is exactly this "
                        + "pole debt plus the sum of the remaining factor orders.")),
                    Paragraph(Text(
                        "Mathlib's punctured-neighborhood criterion then gives both sides: "
                        + "the dictionary product tends to infinity exactly when that total "
                        + "order is negative, and it has no pole exactly when the total order "
                        + "is nonnegative. Thus every possible cancellation is exposed in the "
                        + "remaining finite sum rather than hidden in an analytic slogan.")),
                    Paragraph(Text(
                        "This is the exact structural content that can be certified from the "
                        + "source atom. Its claims about scaled Riemann-zeta zeros, an RH-based "
                        + "exclusion, Hecke-Mahler factor windows, numerical residues, and the "
                        + "three named bricks require external analytic and computational "
                        + "certificates not present in the atom. They are therefore omitted, "
                        + "not promoted to assumptions or asserted without proof. The proof "
                        + "directly uses meromorphicOrderAt_prod, meromorphicOrderAt_zpow, and "
                        + "tendsto_cobounded_iff_meromorphicOrderAt_neg from pinned Mathlib."))),
                DescribeRole.Theorem))));
}
