using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CatalanConjectureSevenRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutes only the printed last clause of Conjecture 7 in arXiv:1811.00248v2 at t = 2, n = 1. "
            + "The values are literature-attested; new_counterexample_claimed = false. "
            + "No claim is made against the intended proposition, its proof, or Cigler's original "
            + "arXiv:1801.05608 statement, whose two terms both use the fifth power here. "
            + "No priority is claimed for the values or identification of the printing error.",
        H("Catalan Conjecture 7 printed-clause refutation"),
        Blocks(
            Paragraph(Text(
                "Wang and Xin, Hankel determinants for convolution powers of Catalan numbers, "
                    + "arXiv:1811.00248v2, printed page 3, Conjecture 7, has second argument 2t "
                    + "in the second Hankel determinant of its last line. The other power in "
                    + "that line is 2t + 1. The original PDF was visually checked on 2026-09-10. "
                    + "The scope sentence gives odd positive r = 2t + 1 and no lower bound on "
                    + "t or n. The formal claim universally quantifies over positive t and all "
                    + "natural n, and retains the printed second argument 2t.")),
            Describe.Lean(
                DescribeId.Create("printed-conjecture-seven-last-clause-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/CatalanConjectureSevenRefutation.result"),
                H("The printed last clause is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At t = 2, n = 1 the left side is H4 of the fifth Catalan power plus H7 "
                        + "of the fourth Catalan power. Their exact values are 5 and minus 4, "
                        + "so the left side is 1 whereas the printed right side is minus 5. "
                        + "The proof reuses the frozen unshifted Hankel definition and defines "
                        + "Catalan powers by Cauchy multiplication. All finite tables are local "
                        + "to the proof. A kernel-checked integer identity L times A equals U, "
                        + "with triangular determinants minus 6 and 24, certifies H7 equals "
                        + "minus 4. Independent integer computations by convolution and Bareiss, "
                        + "and by recurrence and Leibniz expansion, agree; all 14 positive "
                        + "controls from the same paper's Theorems 2 and 3 agree as well. "
                        + "These numerical values are literature-attested: Theorems 2 and 3 "
                        + "on printed page 2 already imply them. Reference 9 is Cigler, Catalan "
                        + "numbers, Hankel determinants and Fibonacci polynomials, arXiv:1801.05608. "
                        + "In its v3, printed page 26, Conjecture 7.2, equation 7.6, both powers "
                        + "are 2k + 1. At k = 2, n = 1 both terms therefore use the fifth power, "
                        + "and 5 plus minus 10 equals minus 5, consistently. "
                        + "The refutation concerns only the 1811.00248v2 printed last clause "
                        + "at t = 2, n = 1. It does not assert that the intended proposition is "
                        + "false or that its proof has a gap, nor that Cigler's corresponding "
                        + "original statement is false. No first discovery of these determinant "
                        + "values or first identification of the printing error is claimed; "
                        + "new_counterexample_claimed = false."))),
                DescribeRole.Theorem)),
        []));
}
