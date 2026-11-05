using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact original output forces an actual grid read on each accumulation endpoint.",
        H("Finite endpoint replay on one rational source"),
        Blocks(
            Paragraph(Text("The source is a positive rational. False denotes L(z)=z/(1+z), true denotes R(z)=z+1, and the head of a word acts first. At chronological prefix w the only read is the complete integer floor of 2^s times the attained response. The original prior is the union, for c=1/6 and c=2/3, of c and all c-1/n for integers n at least 12. Both endpoints are included.")),
            Paragraph(Text("A controller has a common initial local state and a deterministic source-independent instruction function. Instructions halt with a whole output, perform a local step, execute one forward letter on the same source, or request one dyadic floor report and continue from that integer. A Run is a finite derivation of these instructions; it retains the current chronological prefix at every actual read. The state type and instruction function are arbitrary, so the lower bound applies to a class containing every ordinary deterministic finite program. This extensional enlargement is used only for an impossibility result; it does not extract an executable program from an arbitrary function.")),
            Describe.Lean(DescribeId.Create("rational-endpoint-run-grid"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/Source.endpoint_run_requires_grid"),
                H("Every successful endpoint branch reads a grid"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The quantifiers range over every state type, output type, deterministic instruction function, common initial state, target injective on the entire prior, either endpoint, and every finite run ending there. Correctness requires both finite termination on every prior member and equality of every terminal output with its original target. The conclusion supplies a read that actually occurred on the endpoint branch, at its actual attained prefix and requested exponent, where the scaled response is an integer. Merely reaching a dyadic response without reading it is insufficient.")),
                    Paragraph(Text("Each forward letter preserves positivity, order and the upper bound that a response difference is at most the original difference. Away from a dyadic grid, a floor report is constant on a sufficiently small left neighborhood. Induction on the complete finite run takes minima of these neighborhoods and replays local computation, action choices, requested scales, reports and the final output. A sufficiently late member c-1/n belongs to that neighborhood and is a different original. Its identical terminal output contradicts the target's injectivity. The argument uses no uniform bound on scale, work, read count or any resource on other runs.")),
                    Paragraph(Text("The result concerns acquisition of an injective original output on this same rational prior. The attained-prefix classification, exact action minima, explicit acquiring programs and finite transports to the chronological word, named incidence path and indexed prefix table require additional statements."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("C"), Comma, F.Id("V"), Comma, F.Id("i"), Comma, Sp,
        Operatorname, Grp(F.Id("Correct")), Open, F.Id("C"), Comma, F.Id("V"), Close,
        Land, Sp, Operatorname, Grp(F.Id("InjOn")), Open, F.Id("V"), Comma, F.Id("P"), Close,
        Land, Sp, Operatorname, Grp(F.Id("Run")), Open, F.Id("C"), Comma, Seq(F.Id("c"), Underscore, Grp(F.Id("i"))), Comma, F.Id("o"), Comma, F.Id("v"), Comma, F.Id("A"), Close,
        Longrightarrow, Sp, Exists, Sp, Open, F.Id("w"), Comma, F.Id("s"), Close, InMacro, Sp, F.Id("A"), Comma, Sp,
        D(2), Caret, Grp(F.Id("s")), Seq(F.Id("f"), Underscore, Grp(F.Id("w"))), Open, Seq(F.Id("c"), Underscore, Grp(F.Id("i"))), Close, InMacro, Sp, Mathbb, Grp(F.Id("Z"))));
}
