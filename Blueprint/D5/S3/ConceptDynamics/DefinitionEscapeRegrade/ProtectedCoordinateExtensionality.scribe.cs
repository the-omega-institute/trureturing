using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeRegrade;

internal sealed class ProtectedCoordinateExtensionalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeRegrade/"
            + "ProtectedCoordinateExtensionality."
            + "protected_coordinate_dependent_extensionality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All seven dependent protected-coordinate projections jointly determine the frozen record.",
        H("Protected Coordinate Dependent Extensionality"),
        Blocks(Describe.Lean(
            DescribeId.Create("protected-coordinate-dependent-extensionality"),
            DeclarationHandle.Create(Declaration),
            H("Dependent projection agreement characterizes coordinate equality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "ProtectedCoordinateTag has exactly the seven labels targetChain, domain, "
                        + "epsilon, conditions, comparator, baseline, and weightSpec. The "
                        + "dependent projection returns each field in its own type.")),
                Paragraph(Text(
                    "The reverse implication specializes the universal equality at every label "
                        + "and applies structure extensionality. It assumes no decidable equality "
                        + "for any field type."))),
            DescribeRole.Theorem))));

    private static Formula CoordinateType(
        Formula targetChain,
        Formula domain,
        Formula epsilon,
        Formula condition,
        Formula comparator,
        Formula baseline,
        Formula weightSpec) =>
        Call(
            "ProtectedCoordinates",
            targetChain,
            domain,
            epsilon,
            condition,
            comparator,
            baseline,
            weightSpec);

    private static Formula At(Formula coordinates, Formula tag) =>
        Call("protectedCoordinateAt", coordinates, tag);

    private static Formula TheoremFormula()
    {
        Formula targetChain = F.Id("TargetChain");
        Formula domain = F.Id("Domain");
        Formula epsilon = F.Id("Epsilon");
        Formula condition = F.Id("Condition");
        Formula comparator = F.Id("Comparator");
        Formula baseline = F.Id("Baseline");
        Formula weightSpec = F.Id("WeightSpec");
        Formula oldCoordinates = F.Id("oldCoordinates");
        Formula newCoordinates = F.Id("newCoordinates");
        Formula tag = F.Id("tag");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula tagType = Seq(Operatorname, Grp(F.Id("ProtectedCoordinateTag")));
        Formula coordinates = CoordinateType(
            targetChain,
            domain,
            epsilon,
            condition,
            comparator,
            baseline,
            weightSpec);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            targetChain, Comma, Sp,
            domain, Comma, Sp,
            epsilon, Comma, Sp,
            condition, Comma, Sp,
            comparator, Comma, Sp,
            baseline, Comma, Sp,
            weightSpec, Colon, Sp, type, Comma, RowBreak, Grp(),
            oldCoordinates, Comma, Sp, newCoordinates, Colon, Sp,
            coordinates, Comma, RowBreak, Grp(),
            oldCoordinates, Sp, Eq, Sp, newCoordinates,
            Sp, Leftrightarrow, RowBreak, Grp(),
            Forall, Sp, tag, Colon, Sp,
            tagType, Comma, Sp,
            At(oldCoordinates, tag), Sp, Eq, Sp, At(newCoordinates, tag), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
