using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class PerturbedHarmonicWeightsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/PerturbedHarmonicWeights";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An enlarged reference test bounds the weighted collision excess on a perturbed cutoff.",
        H("Collision Budgets for Perturbed Cutoffs and Recomputed Weights"),
        Blocks(
            Paragraph(Text(
                "Let J have decidable equality. Let g and h be real reference and perturbed frequencies, "
                + "with |h(j)−g(j)|≤r(j)≤R. Let V be a finite support containing every index with "
                + "X−R<g(j)≤T+R, and assume r(j)<g(j) on V. Write U for the indices in V "
                + "with X<h(j)≤T. Fix a≥0, a natural degree p and a resolution η≥0.")),
            Paragraph(Text(
                "For a positive ordinate x write w(x)=x/(a+x²). The realized weights u on U "
                + "are w(h(j)). The weights v on V are [g(j)/(g(j)−r(j))]w(g(j)). "
                + "For a finite support A, write E(A,z) for the degree-p near-collision mass "
                + "with frequencies h restricted to A and weights z, minus the diagonal mass.")),
            Describe.Lean(
                DescribeId.Create("collision-excess-le-on-perturbed-cutoff"),
                DeclarationHandle.Create(Owner + ".collision_excess_le_on_perturbed_cutoff"),
                H("Transfer from the enlarged support to the realized cutoff"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displacement bound places every actual cutoff index in the enlarged "
                        + "reference cutoff. On V, write x=g(j), y=h(j) and r=r(j). "
                        + "The inequalities y(x−r)≤y² and y(x−r)≤x² follow from "
                        + "x−r≤y≤x+r. Multiply by the positive denominators and combine "
                        + "these inequalities with a≥0 to obtain u(j)≤v(j). "
                        + "As a uniform factor over a≥0 the factor x/(x−r) is attained "
                        + "when a=0 and y=x−r.")),
                    Paragraph(Text(
                        "Extend each degree vector on U by zero on V. The extension preserves "
                        + "total degree and frequency. It also preserves the multinomial "
                        + "coefficient because the added coordinates have factorial 0!=1. "
                        + "The corresponding monomial product can only increase under "
                        + "the dominating weights. Diagonal subtraction leaves a sum over "
                        + "distinct ordered pairs, whose members stay distinct under the injection. "
                        + "The other terms on V are nonnegative.")),
                    Paragraph(Text(
                        "A bound on the excess for the fixed support and weights therefore "
                        + "applies to the realized test at the same resolution. The frequencies "
                        + "on both supports come from the same perturbation. This transfer applies "
                        + "to comparison spectra for which the enlarged tests have certified budgets."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        var j = F.Id("j");
        var u = F.Id("U");
        var v = F.Id("V");
        var ordinate = new Formula.FunctionCall(FormulaIdentifier.Create("h"), [j]);
        var cutoff = Seq(F.Id("X"), Lt, ordinate, Leq, F.Id("T"));
        var membership = Seq(j, Sp, InMacro, Sp, v);
        var covered = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("j"), F.Id("J"),
            new Formula.Logic(cutoff, FormulaLogicOperator.Implies, membership));
        var small = new Formula.FunctionCall(FormulaIdentifier.Create("E"), [u, F.Id("u")]);
        var large = new Formula.FunctionCall(FormulaIdentifier.Create("E"), [v, F.Id("v")]);
        return Disp(new Formula.Logic(covered, FormulaLogicOperator.And,
            new Formula.Relation(small, FormulaRelationOperator.LessThanOrEqual, large)));
    }
}
