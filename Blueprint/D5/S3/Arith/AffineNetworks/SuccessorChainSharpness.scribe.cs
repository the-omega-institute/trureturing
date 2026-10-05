using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AffineNetworks;

internal sealed class SuccessorChainSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual named successor chain attains the original modular stopping depth.",
        H("Successor-chain stopping sharpness"),
        Blocks(Describe.Lean(
            DescribeId.Create("successor-chain-sharpness"),
            DeclarationHandle.Create(
                "D5/S3/Arith/AffineNetworks/SuccessorChainSharpness.successor_chain_sharpness"),
            H("Original recurrence and complete actual-source transcripts"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural N≥2 and m≥2, the theorem constructs one actual Network C. " +
                    "Its vertex and named-edge types are equivalent to Fin N and Fin (N−1). " +
                    "Edge j has source rank j and destination rank j+1, multiplier 1 and offset 0. " +
                    "The root has rank 0, the last vertex rank N−1, the ambient modulus is m, " +
                    "and exactly the last vertex has port m; every other port is 1.")),
                Paragraph(Text(
                    "The independently defined original gcd/lcm iterate is evaluated for every " +
                    "depth n and every vertex of rank i. It equals 1 when i+n<N−1 and m otherwise. " +
                    "The proof computes the actual outgoing named-edge subtype: empty at the last " +
                    "vertex and a singleton elsewhere. Depth induction propagates the terminal port; " +
                    "no replacement recurrence or assumed path characterization is used.")),
                Paragraph(Text(
                    "Every actual path from v to w satisfies rank(w)=rank(v)+length(path), and " +
                    "its original phase run preserves every t in the full source ZMod m. " +
                    "An actual root-to-last named-edge path is constructed with length N−1. " +
                    "Its terminal port returns the original canonical phase residue and separates " +
                    "the same sources 0 and 1 used in every shorter experiment.")),
                Paragraph(Text(
                    "For every shorter root path, every factorization into a prefix and a suffix " +
                    "has prefix port 1 and equal actual reads for 0 and 1. The empty prefix gives " +
                    "the initial root read; the empty suffix gives the final read of that path. " +
                    "The chronological trace has typed vertex-port events and named-edge events. " +
                    "It starts with the actual root read and appends each actual edge followed by " +
                    "the read of the same continuously transported phase at its destination.")),
                new DocumentBlock.DisplayFormula(TraceFormula()),
                Paragraph(Text(
                    "For every internal-control type K and every deterministic choice function " +
                    "of public vertex, current control and obtained chronological trace, an actual " +
                    "executor is constructed. Choices are either stop or an original legal outgoing " +
                    "arrow with its next control state. The returned state retains the actual path " +
                    "and control. At zero it is the root empty path and the supplied common control; " +
                    "each next step either stays stopped or appends the chosen named arrow. " +
                    "The executed path length is at most the step count. At every count below N−1, " +
                    "both sources produce equal paths, controls, complete chronological traces and " +
                    "next choices. This is proved by induction from actual prefix reads, rather " +
                    "than assuming transcript equality. A common external random seed may be " +
                    "included in K; the theorem states deterministic equality for each fixed seed.")),
                Paragraph(Text("At every shorter depth "),
                    Math(Seq(F.Id("n"), Lt, F.Id("N"), Minus, D(1))),
                    Text(
                        ", the same original root iterate is 1, while its value at N−1 is m≠1. " +
                        "The explicit delayed distinguishing experiment therefore prevents any " +
                        "smaller uniform stopping depth. This statement concerns the prescribed " +
                        "finite full-phase network and history-based legal control. It adds no " +
                        "hidden phase guards, costs or reference channels, and makes no claim " +
                        "about the cost of obtaining a complete behavior boundary."))),
            DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula bound = Seq(F.Id("N"), Minus, D(1));
        return Disp(Seq(
            Forall, Sp, F.Id("N"), Comma, F.Id("m"), Geq, D(2), Comma, Sp,
            Exists, Sp, F.Id("C"), Comma, Call("NamedChain", F.Id("C"), F.Id("N"), F.Id("m")), Land,
            Grp(Forall, Sp, n, Comma, i, Comma,
                Call("iterate", F.Id("C"), n, i), Eq,
                Call("if", Seq(i, Plus, n, Lt, bound), D(1), F.Id("m"))), Land,
            Call("ActualPrefixAgreement", F.Id("C"), D(0), D(1), bound), Land,
            Call("ChronologicalExecutionAgreement", F.Id("C"), D(0), D(1), bound), Land,
            Call("ActualTerminalSeparation", F.Id("C"), D(0), D(1), bound), Land,
            Grp(Forall, Sp, n, Lt, bound, Comma,
                Call("iterate", F.Id("C"), n, D(0)), Eq, D(1), Neq, Sp,
                F.Id("m"), Eq, Call("iterate", F.Id("C"), bound, D(0)))));
    }

    private static Formula TraceFormula() => Disp(Seq(
        Call("trace", Call("nil"), F.Id("t")), Eq,
        OpenBracket, Call("read", F.Id("root"), F.Id("t")), CloseBracket, Semi, Sp,
        Call("trace", Call("cons", F.Id("p"), F.Id("e")), F.Id("t")), Eq,
        Call("trace", F.Id("p"), F.Id("t")), Plus,
        OpenBracket, F.Id("e"), Comma,
        Call("read", Call("dst", F.Id("e")),
            Call("pathRun", Call("cons", F.Id("p"), F.Id("e")), F.Id("t"))), CloseBracket));
}
