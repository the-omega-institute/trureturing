using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class CoordinateDependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dependent coordinates are witnessed by separating pairs with distinct invariant values.",
        H("Coordinate Dependence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dependency-set"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/CoordinateDependence.dependencySet"),
                H("Dependency set"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dependencySet")), Open,
                    Operatorname, Grp(F.Id("separatesAt")), Comma, Sp,
                    Operatorname, Grp(F.Id("invariant")), Close, Sp, Eq, Sp,
                    OpenBrace, F.Id("coordinate"), Sp, Mid, Sp,
                    Exists, Sp, F.Id("left"), Comma, Sp, F.Id("right"), Comma, Sp,
                    Operatorname, Grp(F.Id("separatesAt")), Open,
                    F.Id("coordinate"), Comma, Sp, F.Id("left"), Comma, Sp,
                    F.Id("right"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("invariant")), Open, F.Id("left"), Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("invariant")), Open, F.Id("right"), Close,
                    CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary coordinate, system, and value types, separatesAt records "
                        + "the primitive assertion that two systems form a separating pair at a "
                        + "coordinate. The dependency set contains exactly those coordinates for "
                        + "which such a pair has unequal invariant values.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Function.DependsOn describes factorization through selected "
                        + "product coordinates and is not this separating-pair definition. Repository "
                        + "and pinned-library searches found no matching set-valued declaration, so "
                        + "this definition introduces only the generic abstraction stated here.")),
                    Paragraph(Text(
                        "The Lean module checks both directions of non-hollowness with concrete examples: "
                        + "one relation and invariant make coordinate zero a member, while a constant "
                        + "invariant has the empty dependency set even when every pair separates."))),
                DescribeRole.Definition)),
        []));
}
