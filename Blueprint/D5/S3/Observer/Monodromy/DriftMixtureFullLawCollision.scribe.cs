using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class DriftMixtureFullLawCollisionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/DriftMixtureFullLawCollision."
            + "five_scenario_full_marginal_collision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five bounded positive drift scenarios make the entire setting-wise "
            + "variance laws coincide for the two specified covariance candidates. "
            + "Every test function agrees, not merely a finite list of moments.",
        H("A Full-Marginal Drift Collision"),
        Blocks(
            Paragraph(Text(
                "Reuse the actual four records computed from the pairing, covariance "
                    + "and dual pulse matrices of GainRobustGaussianDiscrimination. "
                    + "The candidates are c=1 and c=1/5. The detector variance gain "
                    + "is exactly one. Five scenarios are equally weighted. "
                    + "Each hypothesis uses the same scenario-specific nonnegative "
                    + "noise offset array, bounded above by three, while its actual "
                    + "positive pulse gains may differ within the same known box.")),
            Describe.Lean(
                DescribeId.Create("five-scenario-full-marginal-collision"),
                DeclarationHandle.Create(Declaration),
                H("No collection of separate-setting distributional tests separates this pair"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem constructs five real arrays: noise, sHi, tHi, "
                            + "sLo and tLo. In every scenario both pulse pairs lie "
                            + "in GainBox(352/353), namely [1/353,705/353] squared. "
                            + "For every setting k and every real test function f, "
                            + "the sum of f evaluated at the five actual conditional "
                            + "variances is the same under the two candidates. "
                            + "Dividing by five gives equality of the uniform "
                            + "finite variance laws.")),
                    Paragraph(Text(
                        "The construction starts with y=sqrt(89901), "
                            + "z=sqrt(180405)-2, s=y/5+2z-201, "
                            + "L=s squared+1-250000-z squared, and r=sqrt(L/48). "
                            + "Squared-endpoint estimates give y in (299,300), "
                            + "z in (422,423), s in (702,705), "
                            + "L in (63876,68942), and r in (36,38). "
                            + "These estimates certify every nonnegative noise "
                            + "and bounded positive gain condition.")),
                    Paragraph(Text(
                        "Before division of pulse gains by 353, the high-candidate "
                            + "pairs are (r,1), (s,1), (1,1), (1,300), (r,1). "
                            + "The low-candidate pairs are (5r,1), (5r,1), "
                            + "(1,y), (z,10), (500,1). The noise numerators, "
                            + "divided by 124609, are L/2, 0, L+250197, "
                            + "L+249999 and L. The actual matrix products yield "
                            + "the four-record scalar formula before this "
                            + "construction is substituted.")),
                    Paragraph(Text(
                        "The low rows match high rows with setting-wise permutations "
                            + "(0,1,2,3,4), (4,0,2,1,3), (0,1,3,2,4), "
                            + "and (4,0,1,3,2). All twenty equalities follow from "
                            + "the two square-root conics and the definitions of "
                            + "s,L,r. Finite sum commutativity then proves equality "
                            + "for an arbitrary f. The permutations differ across "
                            + "settings: joint scenario records are not equated.")),
                    Paragraph(Text(
                        "Applying the same variance-to-output Gaussian channel "
                            + "to each setting gives identical complete homodyne "
                            + "laws, characteristic functions, and all even moments. "
                            + "This measure-theoretic interpretation and the "
                            + "adaptive independent-shot transcript consequence "
                            + "are ordinary arguments in the theory, not additional "
                            + "Lean Gaussian-measure or quantum-state theorems.")),
                    Paragraph(Text(
                        "The example allows noise correlated with the latent "
                            + "calibration and is not a zero-noise counterexample. "
                            + "It proves existence at the displayed finite drift "
                            + "radius, not optimality of that radius or of five "
                            + "scenarios. Extra controls, observed latent labels "
                            + "and shared-calibration paired acquisitions are "
                            + "different observation protocols."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Grouped-sample identifiability has substantial prior art, "
                    + "including Vandermeulen and Scott, arXiv:1502.06644, "
                    + "and Allman, Matias and Rhodes, arXiv:0809.5032. "
                    + "The present contribution is an explicit collision inside "
                    + "the existing four-setting quantum-control record family. "
                    + "No generic mixture theorem, global priority or solution "
                    + "of the Fano monodromy expectation is claimed.")))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement() => Disp(Seq(
        Exists, Sp, F.Id("noise"), Comma, Sp, F.Id("sHi"), Comma, Sp,
        F.Id("tHi"), Comma, Sp, F.Id("sLo"), Comma, Sp, F.Id("tLo"), Comma, Sp,
        Call("FiveScenarioBounds", F.Id("noise"), F.Id("sHi"), F.Id("tHi"),
            F.Id("sLo"), F.Id("tLo")), Sp, Land, Sp,
        Forall, Sp, F.Id("k"), Comma, Sp, F.Id("f"), Comma, Sp,
        new Formula.Relation(Call("HighTestSum", F.Id("k"), F.Id("f")),
            FormulaRelationOperator.Equal,
            Call("LowTestSum", F.Id("k"), F.Id("f")))));
}
