using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Forms;

internal sealed class AuxiliaryPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary Pair", H("Auxiliary Pair"),
        Blocks(
            Paragraph(Text("Finite test datum of the auxiliary pair: sum of translates and transformation law. Auxiliary pair: class-sum lift as conjugate descent; its polynomial is a joint harmonic.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Forms/AuxiliaryPair.theta_eq_smul_star_lift_swap"),
                H("theta_eq_smul_star_lift_swap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a form Ξ on V, the lift θΞ to W is dim V_λ' · [K₀ : level] times the complex conjugate of the descent of conj(F_Ξ) with datum P_{v⁺} ⊗ Υ, where F_Ξ and v⁺ are taken for the parameter AuxPair.paramV.")))))));
}
