using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Automata;

internal sealed class GoldenRatioBase4DfaoMinimalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality."
        + "paper_base4_golden_ratio_dfao_is_not_minimal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 21-live-state partial DFAO refutes the fixed base-4 22-state minimality claim.",
        H("Base-4 Golden-Ratio DFAO Minimality Refuted"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paper-base4-golden-ratio-dfao-is-not-minimal"),
                DeclarationHandle.Create(Declaration),
                H("A 21-live-state counterexample"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Words/barnoffbrightshallit2024using")),
                Blocks(
                    Paragraph(Text(
                        "The candidate is a partial DFAO with 21 live states; an illegal "
                        + "second consecutive one takes the implicit dead transition. "
                        + "It agrees with the paper's 22-state table on every valid "
                        + "Zeckendorf encoding and ignores leading zeroes.")),
                    Paragraph(Text(
                        "Finite table certificates establish output and legal-transition "
                        + "compatibility. Structural induction lifts those certificates to "
                        + "all admissible words, so the result is a universal refutation "
                        + "rather than a finite-prefix match."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("golden-ratio-base4-dfao-minimality"),
                    ResolutionKind.Refuted)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula MainFormula() => Disp(Seq(
        Exists, Sp, F.Id("candidate"), Colon, Sp,
        Call("AdmissibleDFAO", D(2, 1)), Comma, Sp,
        Call("EquivalentOnAdmissibleEncodings",
            Call("machine", F.Id("candidate")), F.Id("paperBase4DFAO")), Dot));
}
