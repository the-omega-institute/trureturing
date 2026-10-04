using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciResonantWindowCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original KBonacci weights give exact distinct-window counts on both resonant phase cosets.",
        H("Resonant parity windows of the original weights"),
        Blocks(
            Paragraph(Text(
                "Fix the original order k at least two and a positive block width m. "
                + "Set T=k+1, g=gcd(m,T) and p=T/g, with g at least two. "
                + "The weight G_n is dbonacci k (n+2), with initial values 2^n for n<k "
                + "and the sum of its preceding k weights thereafter. "
                + "The phase set P is the image of multiplication by g on ZMod T; "
                + "P+1 is its translate by one. A window at a phase theta records the "
                + "actual weights G_(theta.val+i) modulo two for all i in Fin j.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-resonant-window-counts"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciResonantWindowCounts."
                    + "kbonacci_resonant_window_counts"),
                H("Exact counts for every window length"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, F.Id("A"), Underscore, D(0), Eq,
                    F.Id("D"), Underscore, D(0), Eq, D(1), Close, Qquad, Land, Qquad,
                    Sp, Open, Forall, Sp, F.Id("j"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Sp, Open,
                    F.Id("j"), Geq, D(1), Implies, Open,
                    F.Id("A"), Underscore, F.Id("j"), Eq,
                        Min, Open, F.Id("p"), Comma, D(2), Plus,
                            Lfloor, Sp, F.Id("j"), Slash, F.Id("g"), Rfloor, Close,
                        Qquad, Land, Qquad, Sp,
                        F.Id("D"), Underscore, F.Id("j"), Eq,
                        Min, Open, F.Id("p"), Comma, D(1), Plus,
                            Lfloor, Open, F.Id("j"), Plus, D(1), Close, Slash,
                            F.Id("g"), Rfloor, Close, Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A_j and D_j count distinct window vectors, the cardinalities "
                        + "of the actual window images over P and P+1. They count a "
                        + "shared zero vector once when some starts have no visible one. "
                        + "The formulas include p=1, g=2, empty windows and every length "
                        + "beyond a full period.")),
                    Paragraph(Text(
                        "The original recurrence gives G_(n+k+1)+G_n=2G_(n+k). "
                        + "Thus parity has period T and ones exactly at residues zero "
                        + "and k. The cosets are enumerated exactly by qg and qg+1, "
                        + "for zero at most q below p. Their first-one offsets are "
                        + "zero at q=0 and (p-q)g-1 otherwise for P, and (p-q)g-2 "
                        + "for P+1. A visible first one distinguishes its window from "
                        + "every later first hit. All unseen hits yield the same zero "
                        + "window. Ordered first-hit representatives and one possible "
                        + "zero representative give the two image cardinalities."))),
                DescribeRole.Theorem))));
}
