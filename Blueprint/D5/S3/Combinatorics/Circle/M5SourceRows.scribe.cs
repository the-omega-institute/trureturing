using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class M5SourceRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original physical rows of an M5 centered source.",
        H("Original physical rows of an M5 centered source"),
        Blocks(
            Paragraph(Text("The source is s(i)=centered(2^k-1,2^i*t) on physical labels Fin(k). The LARGE threshold is Q=2^(k-2), and C=(2^k-2)/2. Advance means iteration of finRotate(k), retaining all k labels even when the numerical orbit is shorter. An own row consists of its LARGE parent and its literal SMALL interior, ending at the next LARGE label. A length-zero row has no SMALL interior; its seed is still the actual successor of its parent.")),
            Paragraph(Text("OriginalM5 states the positive-hard R1 assumptions directly on this source. The attained least negative magnitude is a, the attained least positive magnitude is b, and a<b<2a. The labels p,d attain the positive maximum and negative minimum. There are five LARGE labels of each sign. The first positive parent is x, followed cyclically by d,beta,gamma,P,J,T,U,V0,D0 and the boundary x. The sorted physical offsets define these labels and all row lengths.")),
            Paragraph(Text("Between LARGE labels the centered recurrence doubles without wrapping. Each signed row therefore has values seed,2*seed,...,2^(length-1)*seed, with sum (2^length-1)*seed. The last value 2^length*seed is the next LARGE terminal. Sorting all actual LARGE offsets and splitting the complete rotated Fin(k) list gives a disjoint exhaustive ten-row partition. The repeated boundary x is excluded from this partition.")),
            Paragraph(Text("The source recurrences give N=H*z+b=H*b+n, z=n+(H-1)*Delta, b=n+H*Delta and b1=n+H^2*Delta, where H=2^(L+1) and Delta=b-z. The hard hypotheses force L>=2 and positive even Delta. These equalities come from the original modular source and its attained extrema."))), []));
}
