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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula CompositionFormula()
    {
        Formula state = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula middleType = F.Id("D");
        Formula fineType = F.Id("E");
        Formula cost = F.Id("cost");
        Formula combine = F.Id("combine");
        Formula compositionBound = F.Id("compositionBound");
        Formula combineMono = F.Id("combineMono");
        Formula qC = F.Id("qC");
        Formula qD = F.Id("qD");
        Formula qE = F.Id("qE");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula hCDName = F.Id("hCD");
        Formula hDEName = F.Id("hDE");
        Formula type = F.Id("Type");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula lawA = F.Id("A");
        Formula lawB = F.Id("B");
        Formula lawC = F.Id("C");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula rPrime = Seq(r, Apos);
        Formula sPrime = Seq(s, Apos);
        Formula compositionBoundLaw = Seq(
            Forall, Sp, lawA, Comma, Sp, lawB, Comma, Sp, lawC, Colon, Sp, type,
            Comma, Sp, p, Colon, Sp, Arrow(lawB, lawC), Comma, Sp,
            q, Colon, Sp, Arrow(lawA, lawB), Comma, Sp,
            Apply("cost", Seq(p, Sp, Circ, Sp, q)), Sp, Leq, Sp,
            Apply("combine", Apply("cost", p), Apply("cost", q)));
        Formula combineMonoLaw = Seq(
            Forall, Sp, r, Comma, Sp, rPrime, Comma, Sp, s, Comma, Sp, sPrime,
            Colon, Sp, naturalNumbers, Comma, Sp,
            r, Sp, Leq, Sp, rPrime, Sp, Rightarrow, Sp,
            s, Sp, Leq, Sp, sPrime, Sp, Rightarrow, Sp,
            Apply("combine", r, s), Sp, Leq, Sp, Apply("combine", rPrime, sPrime));
        Formula hCD = Apply("ResourceRefines", cost, r, qC, qD);
        Formula hDE = Apply("ResourceRefines", cost, s, qD, qE);
        Formula composed = Apply("ResourceRefines", cost,
            Apply("combine", r, s), qC, qE);
        Formula additive = Seq(
            Open, Apply("combine", r, s), Sp, Eq, Sp, r, Plus, s,
            Sp, Rightarrow, Sp,
            Apply("ResourceRefines", cost, Seq(r, Plus, s), qC, qE), Close);
        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, coarseType, Comma, Sp, middleType,
            Comma, Sp, fineType, Colon, Sp, type, Comma, Esc,
            cost, Colon, Sp, F.Id("ResourceCost"), Comma, Sp,
            combine, Colon, Sp, Arrow(naturalNumbers, Arrow(naturalNumbers, naturalNumbers)),
            Comma, Esc,
            compositionBound, Colon, Sp, Grp(compositionBoundLaw), Comma, Esc,
            combineMono, Colon, Sp, Grp(combineMonoLaw), Comma, Esc,
            qC, Colon, Sp, Apply("Concept", state, coarseType), Comma, Sp,
            qD, Colon, Sp, Apply("Concept", state, middleType), Comma, Sp,
            qE, Colon, Sp, Apply("Concept", state, fineType), Comma, Esc,
            r, Comma, Sp, s, Colon, Sp, naturalNumbers, Comma, Esc,
            hCDName, Colon, Sp, hCD, Comma, Sp,
            hDEName, Colon, Sp, hDE, Comma, Esc,
            Open, composed, Sp, Land, Sp, additive, Close, Dot));
    }
}
