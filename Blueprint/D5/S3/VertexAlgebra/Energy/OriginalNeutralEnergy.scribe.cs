using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Energy;

internal sealed class OriginalNeutralEnergyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original normal-product word estimates and orthogonal recombination used by both lattice energy bounds.",
        H("Neutral words and finite energy recombination"),
        Blocks(
            Result("Hm_grade_orthogonal", "Hm grade orthogonal", "For arbitrary original LatticeData D and complex H satisfying both inverse-Gram equations, original u,v in distinct integer Sugawara grades E,F have Hm(u,v)=0. The actual original L0 pairing identity proves the result; the within-grade form remains non-diagonal."),
            Result("normD_orthogonal_sum", "normD orthogonal sum", "For every positive original lattice Gram form, finite index set s and original family f with Hm(f(i),f(j))=0 for distinct indices in s, normD of its sum squared equals the sum of normD(f(i)) squared."),
            Result("energy_power_grade", "energy power grade", "For arbitrary original D,H with both inverse-Gram equations, every integer E, original v in grade E and natural N, (1+L0)^N v=((E:Complex)+1)^N times v."),
            Result("stateEnergies_nonneg", "stateEnergies nonneg", "For every positive original lattice Gram form and original finite v, every integer E in stateEnergies D v is nonnegative, by actual charge-energy positivity and nonnegative oscillator energy."),
            Paragraph(Text("This support module keeps the original private neutral proof components in the OriginalChargedEnergy namespace. Its only original data are LatticeData D, the original Carrier, Hm and normD. Positivity is derived by OriginalCurrentEnergy. For energy recombination the complex H satisfies both inverse equations with gramComplex(D). No diagonal restriction, oscillator cutoff, support bound, alternate carrier or half-frequency form is introduced.")),
            Paragraph(Text("The private original_word_energy_le specializes the single seed-parametrized arbitrary-charge induction in OriginalWordEnergy to charge zero with the literal identity seed (1,0). It estimates literal original normal-product words at a general mode between grades E,F at most M. Its left branch retains negative currents and its right branch retains nonnegative currents. The intermediate derivative strip vanishes by the actual binomial coefficient. Positive energy gives finite branch ranges, with surviving intermediate grades between 0 and M. The recursive constant is K(empty)=1 and K((i,r)::tail)=(r+2)*((r+1)^r/r!)*sqrt(3*G(i,i))*K(tail); the word exponent is weight plus length, at most twice the weight. No factors are commuted and no contractions are dropped.")),
            Paragraph(Text("The polynomial constant is 1+sum_e |coeff(p,e)|*K(occurrences(e)), positive also when p=0. Weighted homogeneity and the literal polynomial field expansion give the fixed-grade neutral bound. The private energy_bound_of_grades uses exact Hm orthogonality of distinct actual Sugawara grades and finite grade projections. Distinct shifted output energies remain orthogonal, so the full finite mixed-state estimate has no input-support multiplier. OriginalNeutralEnergy retains the unchanged private original_neutral_energy_le; OriginalChargedEnergy consumes it to prove its existing public neutral bound and consumes the grade estimate and recombination in the charged bound.")),
            Paragraph(Text("The shared grade orthogonality, power and recombination results directly supply the original Sobolev and heat analysis; the word bounds remain consumed proof components. Existing source suppliers retain their Bakalov-Kac, Matsuo-Nagatomo, Carnahan and Mathlib attributions. Smeared fields, closability, strong locality, full string theory and AdS/CFT remain separate obligations."))),
        []));
    private static DocumentBlock.Describe Result(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("originalneutralenergy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Theorem);
}
