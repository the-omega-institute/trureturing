using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class ChapotonPropositionFiveTwoRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutes only printed Proposition 5.2 in arXiv:2001.01449v1 at n = 1, t = 1; "
            + "literature-attested, new_counterexample_claimed = false. No claim that the "
            + "authors' intended proposition is false or its proof has a gap; P'_n = G_n "
            + "is an interpretation, not the printed text. No verdict on Conjecture 5.4. "
            + "No priority claimed for these values or for identifying the Q' to P' misprint.",
        H("Chapoton and Han Proposition 5.2 printed formula refutation"),
        Blocks(
            Paragraph(Text(
                "Frédéric Chapoton and Guo-Niu Han, On the roots of the Poupard and Kreweras "
                    + "polynomials, arXiv:2001.01449v1, printed page 8, Proposition 5.2, says "
                    + "For every n >= 1, the polynomial Q'_n is the Kreweras polynomial G_n. "
                    + "Rendered source pages 2, 3, 7, 8 and 9 were checked on 2026-09-10. "
                    + "Equation 5.4 defines Q'; the following paragraph defines P' as "
                    + "Q' divided by t minus 1. Both the proposition and proof still print Q'. "
                    + "The formal claim retains the entire polynomial equality for every "
                    + "natural n >= 1. It has no exclusion at n = 1.")),
            Describe.Lean(
                DescribeId.Create("printed-proposition-five-two-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation.result"),
                H("At n = 1 and t = 1 the two sides are zero and two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public rho definition is imported directly from the frozen sister "
                        + "module. Section 5.1 on printed page 7 takes the constant term after "
                        + "floor(d/2) iterations on the fixed index space V_d. Each quotient "
                        + "in equation 5.4 has index 2n minus 1, including zero outer "
                        + "coefficients. At n = 1 the three numerators are 1 minus x squared, "
                        + "zero, and x squared minus 1. Multiplication verifies their exact "
                        + "quotients are minus (1+x), zero, and 1+x. All have index 1, so "
                        + "there are zero operator steps, and their constant coefficients "
                        + "are minus 1, zero, and 1. Thus Q'_1(t) = t squared minus 1. "
                        + "The equation rho(c(1+x)) = c is a derived index-one consequence, "
                        + "not a separately printed premise. Evaluation at 1 gives zero; "
                        + "page 2 prints G_1 = 1+x, whose value at 1 is two. "
                        + "Independent exact checks use integer arrays and monic long "
                        + "division with equation 2.1, and signed geometric sums with the "
                        + "symmetric-basis products of equation 2.2. Both give Q'_1 "
                        + "coefficients (-1,0,1), Q'_2 coefficients (-2,-2,0,2,2), and "
                        + "Q'_3 coefficients (-12,-12,-8,0,8,12,12), in ascending order. "
                        + "Dividing Q' by t minus 1 gives P'_1 through P'_4 equal to the "
                        + "four G polynomials printed on page 2, coefficient by coefficient. "
                        + "Their ascending coefficient lists are (1,1), (2,4,4,2), "
                        + "(12,24,32,32,24,12), and (136,272,384,448,448,384,272,136). "
                        + "Independent G computations use equation 1.3 and equation 2.2 "
                        + "at D = 2. Section 5.1's example (1,1,1,1,1) to (3,4,3) to (4) "
                        + "also agrees, as do all 36 entries printed in equation 5.6. "
                        + "There are 1239 checked exact divisions, zero control mismatches "
                        + "and no floating point. Matrix entries are controls only. "
                        + "The 2020 published version, Moscow Journal of Combinatorics and "
                        + "Number Theory 9, pages 163-172, DOI 10.2140/moscow.2020.9.163, "
                        + "still prints Q'_n in Proposition 5.2 and Q'_1 is 1+x in its proof "
                        + "on page 171. Page 170 prints equation 5-4 and Q'_n(1)=0; "
                        + "page 164 prints G_1=1+x. The actual values are therefore "
                        + "literature-attested. No separate formal erratum was located in "
                        + "the documented search scope as of 2026-09-10; this is a bounded "
                        + "search statement. new_counterexample_claimed = false. "
                        + "Only the printed assertion at n=1,t=1 is refuted. No claim is "
                        + "made that the authors' intended proposition is false or its proof "
                        + "has a gap. P'_n=G_n is the suggested interpretation, not the "
                        + "printed text and not a universal theorem proved here. No verdict "
                        + "is given on Conjecture 5.4. Neither first discovery of the values "
                        + "nor first identification of this Q' to P' misprint is claimed. "
                        + "The formal calculation uses exact rational polynomial arithmetic. "
                        + "All finite equalities are local to the proof."))),
                DescribeRole.Theorem)),
        [],
        anchors:
        [
            Anchor.ParseCanonical("mathlib/module/Mathlib.Tactic.NormNum"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Tactic.Ring")
        ]));
}
