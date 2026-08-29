using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeRegrade;

internal sealed class CoordinateWitnessBundleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle."
            + "has_closed_coordinate_witness_bundle_iff_ne";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed nonempty coordinate witnesses exactly record changed protected coordinates.",
        H("Closed Coordinate Witness Bundle Characterization"),
        Blocks(Describe.Lean(
            DescribeId.Create("closed-coordinate-witness-bundle-characterization"),
            DeclarationHandle.Create(Declaration),
            H("Closed nonempty coordinate witnesses characterize record change"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "CoordinateWitnessBundle records a finite set of changed labels and proves "
                        + "every registered dependent projection differs. Closed supplies the "
                        + "converse inclusion, while the existence predicate requires nonemptiness.")),
                Paragraph(Text(
                    "The reverse implication scans exactly the seven protected-coordinate "
                        + "labels using the supplied decidable equalities. If that scan were "
                        + "empty, frozen dependent extensionality would force the records equal."))),
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
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
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
            OpenBracket, Call("DecidableEq", targetChain), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", domain), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", epsilon), CloseBracket,
            Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", condition), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", comparator), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", baseline), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", weightSpec), CloseBracket,
            Comma, RowBreak, Grp(),
            oldCoordinates, Comma, Sp, newCoordinates, Colon, Sp,
            coordinates, Comma, RowBreak, Grp(),
            Call(
                "HasClosedCoordinateWitnessBundle",
                oldCoordinates,
                newCoordinates),
            Sp, Iff, RowBreak, Grp(),
            oldCoordinates, Sp, Neq, Sp, newCoordinates, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
