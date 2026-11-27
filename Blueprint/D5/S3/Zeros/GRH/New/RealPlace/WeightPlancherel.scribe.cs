using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class WeightPlancherelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight Plancherel", H("Weight Plancherel"),
        Blocks(
            Paragraph(Text("Three weight integrals and sliced Plancherel bounds on quadrics and Heisenberg radicals.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/WeightPlancherel.parseval_heisenbergMeasure_of_box"),
                H("parseval_heisenbergMeasure_of_box"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Plancherel on 𝒩_a. For a kernel k twisted by d with (fw(dsd⁻¹) − fw(s^ε))/g = ξ·fw(s) on 𝒩_a (fw = simpleRootSum), let Φ(n) ≤ C|k_{a+1}(n^ε x, ny)|² vanish off a set S centred as in the hypothesis h. Then ∫Φ dη_a ≤ C(c/md(ξu))^{|ι|} fl_a(u) Λ^{100(ϱ+1)(i+j+31)} ∫|k_{a+2}(σx, σy)|² dθ_{a+1}.")))))));
}
