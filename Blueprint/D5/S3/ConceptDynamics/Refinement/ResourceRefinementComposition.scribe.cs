using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class ResourceRefinementCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resource-bounded factorization witnesses compose under a monotone cost model.",
        H("Resource Refinement Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resource-refines"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition."
                        + "ResourceRefines"),
                H("Resource-bounded refinement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ResourceRefines is the source factorization relation with a public "
                        + "natural-valued budget: a recovery map witnesses the factorization "
                        + "and its cost is at most that budget."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("resource-refinement-compose"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition."
                        + "resource_refinement_compose"),
                H("Resource refinement composes"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public cost-model hypotheses say that composing two recovery maps "
                            + "costs no more than the declared combination of their costs, and "
                            + "that the combination is monotone in each budget.")),
                    Paragraph(Text(
                        "The composed recovery map is the ordinary function composite. The first "
                            + "conclusion gives the combined budget; when the model chooses the "
                            + "additive rule, the second conclusion gives the stated r + s budget.")),
                    Paragraph(Text(
                        "The canonical Concept and factorization vocabulary is imported from the "
                            + "existing ConceptDynamics family; no sibling carrier or relation is "
                            + "redeclared."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula CompositionFormula()
    {
        Formula cost = F.Id("cost");
        Formula combine = F.Id("combine");
        Formula qC = F.Id("qC");
        Formula qD = F.Id("qD");
        Formula qE = F.Id("qE");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula compositionBound = F.Id("compositionBound");
        Formula combineMono = F.Id("combineMono");
        Formula hCD = Apply("ResourceRefines", cost, r, qC, qD);
        Formula hDE = Apply("ResourceRefines", cost, s, qD, qE);
        Formula composed = Apply("ResourceRefines", cost,
            Apply("combine", r, s), qC, qE);
        Formula additive = Seq(
            Open, Apply("combine", r, s), Sp, Eq, Sp, r, Plus, s, Close,
            Sp, Rightarrow, Sp,
            Apply("ResourceRefines", cost, Seq(r, Plus, s), qC, qE));
        Formula hypotheses = Seq(
            compositionBound, Sp, Land, Sp, combineMono, Sp, Land, Sp,
            hCD, Sp, Land, Sp, hDE);

        return Disp(Seq(
            Forall, Sp, cost, Comma, Sp,
            Forall, Sp, combine, Comma, Sp,
            Forall, Sp, qC, Comma, Sp,
            Forall, Sp, qD, Comma, Sp,
            Forall, Sp, qE, Comma, Sp,
            Forall, Sp, r, Comma, Sp,
            Forall, Sp, s, Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp,
            Grp(Seq(composed, Sp, Land, Sp, additive)), Dot));
    }
}
