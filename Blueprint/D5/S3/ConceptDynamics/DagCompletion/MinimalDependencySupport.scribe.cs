using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class MinimalDependencySupportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a monotone finite support property, inclusion minimality is equivalent to failure "
            + "after every single deletion.",
        H("Minimal Dependency Support"),
        Blocks(Describe.Lean(
            DescribeId.Create("inclusion-and-deletion-minimality-coincide"),
            DeclarationHandle.Create(Prefix + "inclusionMinimal_iff_deletionMinimal"),
            H("Inclusion and deletion minimality coincide"),
            StatementSource.FromAuthor(MinimalityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a property of finite coordinate supports be monotone under inclusion. "
                        + "For any finite support, full inclusion minimality is equivalent to the "
                        + "failure of the property after deleting each selected coordinate.")),
                Paragraph(Text(
                    "Decidable equality is retained as an instance binder because deletion uses "
                        + "Finset.erase. Monotonicity remains an explicit antecedent."))),
            DescribeRole.Theorem))));

    private static Formula MinimalityFormula()
    {
        Formula property = F.Id("property");
        Formula support = F.Id("support");
        Formula consequence = Seq(
            Call("InclusionMinimalSupport", property, support), Sp, Iff, Sp,
            Call("DeletionMinimalSupport", property, support));

        return Disp(Seq(
            Forall, Sp, property, Colon, Sp,
            Call("Finset", F.Id("Coordinate")), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            support, Colon, Sp, Call("Finset", F.Id("Coordinate")), Comma,
            RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", F.Id("Coordinate")), CloseBracket,
            Comma, RowBreak, Grp(),
            Call("MonotoneSupport", property), Sp, Rightarrow, RowBreak, Grp(),
            Open, consequence, Close, Dot));
    }
}
