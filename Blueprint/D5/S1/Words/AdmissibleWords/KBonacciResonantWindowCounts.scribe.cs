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
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Conditional all-phase application: equation (35)"), Blocks(
                Paragraph(Text(
                    "Fix any k at least two, put T=k+1, and let c map the natural "
                    + "numbers to ZMod 2. Assume explicitly, for every natural n, "
                    + "c(n)=1 if n modulo T is zero or k, and c(n)=0 otherwise. "
                    + "For every natural length j and every theta in ZMod T, define "
                    + "the actual coordinate window W_j(theta)(i)=c(theta.val+i.val) "
                    + "for i in Fin j. Let R_j be the cardinality of the image of W_j "
                    + "over all of ZMod T. Under this binary-pattern premise, the "
                    + "conditional form of equation (35) is R_0=1, R_1=2 and "
                    + "R_j=min(k+1,j+2) for every j at least two.")),
                Paragraph(Text(
                    "The reusable counting argument is already present in the proof "
                    + "of kbonacci_resonant_window_counts: hfirst supplies the first "
                    + "one at offset h for a positive start s with s+h=k; hfiber "
                    + "separates windows with strictly increasing first-hit offsets; "
                    + "hcount counts an image after the invisible tail collapses to "
                    + "the zero vector. These are local proof blocks, and the "
                    + "correspondence below reuses their expanded arguments. It is "
                    + "not a direct application of the public resonant theorem with "
                    + "g=1: that theorem requires g=gcd(m,T) at least two.")),
                Paragraph(Text(
                    "Enumerate the tail phases k,k-1,...,1 by indices 0 at most r "
                    + "below k. In the first-hit argument set S(r)=k-r and H(r)=r, "
                    + "and put V_j(r)(i)=c(S(r)+i.val). Each S(r) is positive and "
                    + "below T, so its cast to ZMod T has value S(r). Thus these "
                    + "are precisely the actual windows on the tail phases. Since "
                    + "S(r)+H(r)=k, the binary premise gives a one at H(r) and "
                    + "zero at every earlier offset. The offsets H(r)=r are "
                    + "strictly increasing.")),
                Paragraph(Text(
                    "For r<s<k with r<j, coordinate r belongs to Fin j and has "
                    + "value one in V_j(r) and zero in V_j(s); this is exactly the "
                    + "visible-first-hit separation used by hfiber. If j at most r, "
                    + "every coordinate in V_j(r) precedes its first hit, so the "
                    + "whole window is zero. The hcount parameter correspondence "
                    + "is p=k, v=j and F=V_j, with the same window length j. "
                    + "Its representatives have indices below N=min(k,j+1). "
                    + "When N<k, N=j+1 and every omitted index collapses to "
                    + "the zero representative r=j. Separation makes the retained "
                    + "representatives distinct, giving exactly min(k,j+1) tail "
                    + "windows, including lengths beyond T.")),
                Paragraph(Text(
                    "For j at least two the remaining phase zero starts with the "
                    + "two coordinates 10, since k at least two makes c(1)=0. "
                    + "The tail representative r=0 starts at k and begins 11, "
                    + "because k+1 is zero modulo T; every r at least one starts "
                    + "between 1 and k-1 and begins with zero. Thus the first two "
                    + "coordinates distinguish W_j(0) from every tail window, "
                    + "including when k=2. The full image is the insertion of this "
                    + "one additional window into the tail image, so its cardinality "
                    + "is 1+min(k,j+1)=min(k+1,j+2). No upper bound on j is used.")),
                Paragraph(Text(
                    "At j=0 all phase windows are the unique empty function. "
                    + "At j=1 the premise allows only zero and one, and phases "
                    + "1 and 0 realize them respectively, so there are exactly "
                    + "two windows. The premise is inhabited for each k at least "
                    + "two by the sequence defined by the displayed residue rule; "
                    + "the argument does not assume a primitive period.")),
                Paragraph(Text(
                    "This application concerns only the conditional window count "
                    + "in equation (35) of KBONACCI_MINIMAL_MODULAR_OBSERVER. "
                    + "Identifying c with a native scalar readout and certifying "
                    + "its minimum period in equation (34) are separate obligations. "
                    + "The count does not establish actual-history reachability, "
                    + "autonomous minimality or the sharp future horizon asserted "
                    + "in equation (36). It records an application of the existing "
                    + "first-hit and truncated-image machinery, with no claim "
                    + "of new formal mathematical content or literature novelty.")))))));
}
