using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class PermissionIntersectionLeastDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficient intersection is the unique least sufficient permission bundle.",
        H("Unique Least Permission Bundle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sufficient-intersection-is-unique-least"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Sufficiency/PermissionIntersectionLeast."
                        + "sufficient_intersection_is_unique_least"),
                H("A sufficient intersection is the unique least sufficient bundle"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be the type of permission atoms. A permission bundle is a subset "
                            + "of K, and Sufficient is an arbitrary predicate on such bundles. "
                            + "The distinguished bundle is constructed canonically as the "
                            + "intersection of every bundle satisfying that predicate.")),
                    Paragraph(Text(
                        "If this intersection is itself sufficient, membership in the "
                            + "intersection makes it a subset of every sufficient bundle. Thus "
                            + "it is least among them. Any other least sufficient bundle contains "
                            + "and is contained in the intersection, so antisymmetry proves it is "
                            + "the same bundle.")),
                    Paragraph(Text(
                        "The public statement exposes both the leastness of the canonical "
                            + "intersection and unique existence of a least bundle. It assumes no "
                            + "upward-closure law; the source describes that law only as typical, "
                            + "outside the named theorem.")),
                    Paragraph(Text(
                        "Repository search found no exact theorem or duplicate permission "
                            + "primitive. The Lean proof directly applies Mathlib's "
                            + "sInter_subset_of_mem lemma and then subset antisymmetry."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula atoms = F.Id("K");
        Formula bundle = F.Id("P");
        Formula candidate = F.Id("Q");
        Formula sufficient = F.Id("Sufficient");
        Formula bundleType = Seq(Mathcal, Grp(F.Id("P")), Open, atoms, Close);
        Formula family = Seq(
            OpenBrace, bundle, Sp, InMacro, Sp, bundleType, Sp, Mid, Sp,
            Call("Sufficient", bundle), CloseBrace);
        Formula intersection = Call("sInter", family);
        Formula leastIntersection = Call("IsLeast", family, intersection);
        Formula uniqueLeast = Seq(
            Exists, Bang, Sp, candidate, Sp, InMacro, Sp, bundleType, Comma, Sp,
            Call("IsLeast", family, candidate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, atoms, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            sufficient, Colon, Sp, bundleType, Sp, To, Sp,
            Operatorname, Grp(F.Id("Prop")), Comma, RowBreak, Grp(),
            Call("Sufficient", intersection), Sp, Rightarrow, Sp,
            leastIntersection, Sp, Land, RowBreak, Grp(),
            uniqueLeast, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
