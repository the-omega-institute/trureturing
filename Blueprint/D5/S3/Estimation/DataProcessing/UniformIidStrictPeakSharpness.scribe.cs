using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class UniformIidStrictPeakSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform independent letter sources approach the unattained finite strict-peak lower endpoint.",
        H("Uniform Strict Peaks and the Sharp Finite Infimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-peak-sharpness"),
            DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/UniformIidStrictPeakSharpness.uniform_peak_sharpness"),
            H("Exact source formulas, signs and limiting infimum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For a positive integer q, each ordered letter in Fin q has probability 1/q. The five-mode law is the pushforward of five independent draws through the original strict-peak classifier. Relabeling the alphabet from 0,...,q-1 to 1,...,q preserves every strict comparison. Write X=modeLaw(1)+modeLaw(3), kappa=modeLaw(3), and D=modeLaw(0)modeLaw(3)-modeLaw(1)modeLaw(2).")),
                Paragraph(Text("The exact formulas are X=(q-1)(2q-1)/(6q^2), kappa=X(2q^2-2q+1)/(5q^2), and D=-(q-1)(2q-1)(2q^4-13q^3+9q^2-5q+1)/(180q^6). For 2<=q<=5, D is positive; for q>=6 it is negative. Thus these independently specified finite sources exhibit both signs.")),
                Paragraph(Text("As q tends to infinity, D tends to -1/45. Over the set of determinants of all nonnegative normalized finite ordered letter laws, -1/45 is the greatest lower bound and is not a member. The lower bound and nonattainment use FiniteIidStrictPeakLower; the uniform sequence establishes sharpness. Together with the Borel lower surface D>=-X/15, this gives the sharp universal lower bounds D>=-X/15 and D>=-1/45, while neither D>=0 nor D<=0 holds for every iid source.")),
                Paragraph(Text("Conditioning on a letter i gives lowerMass(i)=i/q. A wing above valley c has mass (q(q-1)-c(c+1))/(2q^2). Summing its square over the valley and applying Mathlib's Bernoulli power-sum formula yields the joint peak probability. The determinant sign follows from the quartic expanded about q=6; the limit follows by writing the exact determinant as a polynomial in 1/q. These counting identities belong to the classical strict up-down-word setting; no claim of literature priority is made."))),
            DescribeRole.Theorem))));
}
