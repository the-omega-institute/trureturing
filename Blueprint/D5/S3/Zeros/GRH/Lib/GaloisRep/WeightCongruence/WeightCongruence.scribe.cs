using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.WeightCongruence;

internal sealed class WeightCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight Congruence", H("Weight Congruence"),
        Blocks(
            Paragraph(Text("Ultrametric Stone-Weierstrass for modules; density of matrix coefficients of lacunary weights. The l-adic model of an algebraic modular form: weight moved to l. Chebotarev uniqueness: a Hecke system determines the trace of attached representations. A form is an l-adic uniform limit of typed forms with free weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/WeightCongruence/WeightCongruence.padicModel_mem_uniformClosure"),
                H("padicModel_mem_uniformClosure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let K ≤ K_0 be open, θ a smooth character of K, and let d ∈ K with z_τ(d) = 1 on T fix f, θ(d) = 1. Then the l-adic model of f is a uniform limit from any span containing the equivariant images of models of θ-eigenforms of weight free on T, κ elsewhere.")))))));
}
