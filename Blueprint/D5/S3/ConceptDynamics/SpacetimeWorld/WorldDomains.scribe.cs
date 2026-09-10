using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeWorld;

internal sealed class WorldDomainsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit world domains preserve coordinate typing and guarded legality.",
        H("Dependent Worlds and Typed Images"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guarded-domain"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.guarded_nonempty_iff"),
                H("A guard changes the domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Worlds are the actual subtype of a nonempty set of dependent valuations. The restricted domain is nonempty exactly when some original world satisfies the guard. The equivalence of guarded subtypes passes both membership proofs to any partial operation; no value is supplied outside that domain. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("world-exclusion"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.world_exclusion_eq_guarded"),
                H("Logical exclusion is a domain restriction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("World exclusion removes worlds in the valuation domain. Selection-family exclusion instead removes elements of the native selection space, while contribution complement changes each selected event subset within its retained context. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("family-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.complement_family_readouts"),
                H("Native complement acts on a family by direct image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Possible readouts use the merged native Context, Selection and q. Applying native complement to a family changes its readout image by background minus readout. Family exclusion instead takes the complement of the set of possible selections. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-and-zero"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.incompatible_image_ne_zero"),
                H("Empty constraints are distinct from a zero-valued model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constant zero image on a compatible nonempty domain is the singleton containing zero. The image of the empty domain is empty, and those images differ. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem))));
}
