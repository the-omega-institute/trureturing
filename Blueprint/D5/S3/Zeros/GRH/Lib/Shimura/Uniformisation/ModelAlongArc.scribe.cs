using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class ModelAlongArcDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Model Along Arc", H("Model Along Arc"),
        Blocks(
            Paragraph(Text("Linear maps to the torsion module come from finite-adelic matrices. Objects modelled on theta tori: uniformisation, torsion points, Weil pairing, multiplier. Isogenies of modelled PEL abelian varieties correspond to rational matrices. Analytic families of period maps; theta coordinates vary holomorphically after scaling. Uniformisation of the generic fibre extends over a valuation ring by properness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc.exists_model_over_arc"),
                H("exists_model_over_arc"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let y be an object over a valuation ring O with fraction field ℂ and x its generic fibre. A model of x on (g, ℓ) gives a model of y on (g, ℓ) whose sections π'(w) restrict to π(w) at the generic point.")))))));
}
