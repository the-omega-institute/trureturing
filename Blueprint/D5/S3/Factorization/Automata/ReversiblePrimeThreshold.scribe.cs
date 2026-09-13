using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class ReversiblePrimeThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact division can reveal arbitrarily deep prime-exponent information.",
        H("Reversible Prime Inputs Need Unbounded Predictive State"),
        Blocks(
            Paragraph(Text(
                "Fix an actual prime p and positive threshold a. The full integer register "
                + "starts at 1. Input true multiplies by p; input false divides by p only if "
                + "p divides the current integer. The output asks only whether p^a divides "
                + "the reached value. No capacity bound or external digit input is present.")),
            Paragraph(Text(
                "numberStep defines these guarded integer operations, primeBase uses the "
                + "existing PartialDFA carrier, legal contains executable words, and target "
                + "is the Boolean arithmetic property at the reached integer. A private "
                + "commuting-run proof transports this actual evolution through e -> p^e; "
                + "the exponent counter is a proved coordinate system, not an assumed model.")),
            Describe.Lean(
                DescribeId.Create("reversible-prime-no-finite-threshold-dfao"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/ReversiblePrimeThreshold.no_finite_dfao_for_exact_prime_division"),
                H("No finite DFAO computes the threshold on every legal word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("FiniteCorrectDFAO"), Open, F.Id("p"), Comma,
                    F.Id("a"), Close, Sp, Rightarrow, Sp, F.Id("False")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any H, choose H+1 prefixes consisting of a+i multiplications, "
                        + "for 0<=i<=H. They reach the actual integers p^(a+i) and all currently "
                        + "satisfy the threshold. To compare i<j, append i+1 exact divisions "
                        + "to both. Both suffixes are executable: the first reaches p^(a-1), "
                        + "which fails the threshold, while the second still satisfies it. "
                        + "Thus every finite family gives distinct reached states in any "
                        + "correct DFAO. Taking H equal to its state count is impossible.")),
                    Paragraph(Text(
                        "The contradiction uses only common legal continuations. It does "
                        + "not rely on the machine classifying undefined division attempts. "
                        + "It excludes neither a fixed bounded prime register nor an automaton "
                        + "given a fresh binary or Zeckendorf encoding of the current integer. "
                        + "One actual trajectory can exist while a finite observation fails "
                        + "to retain enough information to update the target."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Automata/TypedPartialDFAOOverBase")),
        ]));
}
