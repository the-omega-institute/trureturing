using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class OrderedBirthPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FibonacciAtomic/LocalWiring/OrderedBirthPrefix.";
    private static Formula N => F.Id("n");
    private static Formula Indexed(string head, Formula index) => Seq(F.Id(head), Underscore, Grp(index));
    private static Formula Bits(Formula upper) =>
        Seq(Open, Indexed("z", F.Id("j")), Close, Underscore,
            Grp(Seq(D(1), Le, Sp, F.Id("j"), Le, Sp, upper)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a completed cut of the fixed locally wired source, physical incidence recovers exactly "
        + "the mature marked birth word. Full labels additionally recover the newest marks.",
        H("Exact mature and full chronological birth prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gpo-exact-ordered-birth-prefix"),
                DeclarationHandle.Create(Prefix + "exact_ordered_birth_prefix"),
                H("Physical incidence and its exact mature prefix"),
                StatementSource.FromAuthor(Disp(Seq(
                    Indexed("S", N), Sp, Leftrightarrow, Sp, Open, N, Comma, Sp,
                    Bits(Indexed("v", N)), Close, Quad, Sp,
                    Indexed("X", N), Sp, Leftrightarrow, Sp, Open, N, Comma, Sp,
                    Bits(Indexed("B", N)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem concerns attained cuts n≥2 from the actual known alpha seed. "
                        + "Physical incidence is the prefix closure of the terminal frontier, and "
                        + "the frontier is the set of maximal physical addresses. Either finite "
                        + "representation reconstructs the same ordered physical shape. Its leaf "
                        + "count gives the completed epoch; no timestamp is supplied to the inverse.")),
                    Paragraph(Text(
                        "Use the actual two-step decoder, then the shape of the second step to "
                        + "recover the intermediate labelled tree. Rewinding that tree and reading "
                        + "each old beta batch in physical left-first order recovers the actual "
                        + "mature marked events, including the original update and parent of every "
                        + "birth. Conversely the mature prefix replays to that intermediate state "
                        + "and determines the next physical incidence independently of the newest bits.")),
                    Paragraph(Text(
                        "Full labels permit the same rewind and readback through the current cut. "
                        + "The finite prefix replay and reconstruction agree in both directions "
                        + "on prefixes of the required lengths. For fixed incidence, every assignment "
                        + "of the newest F_(n−1) bits gives one labelled state, and nothing else is "
                        + "undetermined by the mature prefix.")),
                    Paragraph(Text(
                        "The marked word is the specific source birth chronology, not a new observer "
                        + "read port, a generator identification result, or a claim that incidence "
                        + "has already been acquired."))),
                DescribeRole.Theorem))));
}
