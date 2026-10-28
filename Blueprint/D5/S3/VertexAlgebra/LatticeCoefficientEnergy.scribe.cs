using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeCoefficientEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Energy support of the original lattice state-field map without a Gram inverse.",
        H("Inverse-free lattice coefficient energy"),
        Blocks(
            Paragraph(Text("D is the original LatticeData: an arbitrary finite rank with symmetric integral Gram matrix and even diagonal. Singular, indefinite and rank-zero matrices remain in scope. The carrier, canonical sector coefficients, all-state map LatticeAllStateField.Y, oscillatorEnergy, chargeEnergy and grade are the original constructions. No substitute field or grading is introduced.")),
            Describe.Lean(
                DescribeId.Create("lattice-coefficient-energy-actual-mode-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeCoefficientEnergy.actual_mode_grade"),
                H("All-state energy grading for every signed mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original D, m,n,q in Z and a,b in Carrier(D), if a belongs to grade(D,m) and b belongs to grade(D,n), then the actual normalized mode ((Y(D,a))[[q]])(b) belongs to grade(D,m+n-q-1). The two grade memberships are the only hypotheses. All finite charge and oscillator components are included, and the zero state and negative grades and modes are retained.")),
                    Paragraph(Text("Write E for oscillatorEnergy and W(omega) for the sum of k+1 over the descendant word. The private support invariant states that the literal coefficient wordCoeff(D,alpha,beta,omega,q,e,d), with output e first and input d second, vanishes unless E(e)=E(d)+W(omega)-q-1-bilinear(D,alpha,beta). For an empty word and zero input, negative creation index gives the zero polynomial; a nonnegative index uses the existing weighted homogeneity of the original creation coefficient. Input-degree induction uses the exact translation recurrence. Word induction uses the complete finite normal-product recurrence: creation removes output weight j+k+1 and shifts q by j; the charge zero mode occurs at j=k; annihilation removes input weight j-k and shifts q by -j-1. Each summand separately has the asserted energy support.")),
                    Paragraph(Text("The original canonical monomial/word identity and the existing occurrence-weight identity convert this invariant into a rule for the actual charge-labelled monomial basis. The integral identity chargeEnergy(alpha+beta)=chargeEnergy(alpha)+chargeEnergy(beta)+bilinear(alpha,beta) follows from the original doubling identity, bilinearity and symmetry. Charge homogeneity and induction over both full homogeneous basis spans prove the stated all-state rule. All private support and arithmetic helpers are consumed on that proof path."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is a repository-derived recurrence proof on the existing construction. The suppliers retain the Bakalov--Kac lattice-field, Matsuo--Nagatomo normal-product and Carnahan formal vertex-operator attributions; Mathlib supplies finite support, polynomial homogeneity and linear span induction. No external-literature novelty is claimed.")),
            Paragraph(Text("This result concerns coefficient energy support, including degenerate Gram matrices. It does not construct a Sugawara inverse or identify grades with its zero-mode eigenspaces in the degenerate case. The inverse-dependent Sugawara results remain in their original scope. Analytic channel identification, full sewing, a Monster realization, string theory and AdS/CFT remain separate mathematical obligations."))),
        []));
}
