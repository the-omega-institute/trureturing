using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class RequiredComponentDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/RequiredComponentDeletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a presentation component preserves a theorem's eligibility exactly when "
            + "that component is not among the theorem's requirements.",
        H("Required Component Deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("required-component-deletion-iff"),
                DeclarationHandle.Create(Prefix + "required_component_deletion_iff"),
                H("Exact eligibility criterion after deletion"),
                StatementSource.FromAuthor(DeletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Eligibility means that every component required by a theorem occurs in "
                            + "the presented component set. After removing c, this condition is "
                            + "equivalent to prior eligibility together with the absence of a "
                            + "requirement edge from the theorem to c.")),
                    Paragraph(Text(
                        "Both directions are retained. Thus the result proves loss of statement "
                            + "eligibility for a listed load-bearing component and also proves that "
                            + "deleting a genuinely unused component is harmless.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found set and dependency analogues "
                            + "but no theorem with this exact quantified deletion criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("required-component-deletion-can-be-strict"),
                DeclarationHandle.Create(Prefix + "required_component_deletion_can_be_strict"),
                H("A required deletion really destroys eligibility"),
                StatementSource.FromAuthor(StrictWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean presentation supplies a constructive countermodel to any claim "
                        + "that deletion is always harmless: true is required, all components are "
                        + "initially present, and deleting true makes eligibility fail."))),
                DescribeRole.Theorem))));

    private static Formula DeletionFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Eligible")), Open,
        F.Id("present"), Sp, Setminus, Sp, OpenBrace, F.Id("c"), CloseBrace, Comma, Sp,
        F.Id("t"), Close, Quad, Iff, Quad,
        Operatorname, Grp(F.Id("Eligible")), Open, F.Id("present"), Comma, Sp, F.Id("t"), Close,
        Quad, Land, Quad, Neg, F.Id("requires"), Open, F.Id("t"), Comma, Sp, F.Id("c"), Close));

    private static Formula StrictWitnessFormula() => Disp(Seq(
        Exists, Sp, F.Id("requires"), Comma, Sp, F.Id("present"), Comma, Sp,
        F.Id("t"), Comma, Sp, F.Id("c"), Comma, Quad,
        Operatorname, Grp(F.Id("Eligible")), Open, F.Id("present"), Comma, Sp, F.Id("t"), Close,
        Quad, Land, Quad, F.Id("requires"), Open, F.Id("t"), Comma, Sp, F.Id("c"), Close,
        Quad, Land, Quad, Neg, Operatorname, Grp(F.Id("Eligible")), Open,
        F.Id("present"), Sp, Setminus, Sp, OpenBrace, F.Id("c"), CloseBrace,
        Comma, Sp, F.Id("t"), Close));
}
