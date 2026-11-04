using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class QuadraticPrefixParityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A disjoint sigma union applies the sign-product rule with exact multiplicities. The central interval lengths sum to m(m+1). The resulting integral congruence modulo4 supplies quotient parity; reflection supplies the even square norm. These are consumed in both prime families.", H("QuadraticPrefixParity"), Blocks(
            Paragraph(Text("A disjoint sigma union applies the sign-product rule with exact multiplicities. The central interval lengths sum to m(m+1). The resulting integral congruence modulo4 supplies quotient parity; reflection supplies the even square norm. These are consumed in both prime families.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-sign-rows-mod-four"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.sign_rows_mod_four"), H("sign_rows_mod_four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Applying the sign rule to a genuine disjoint union counts repeated signs with multiplicity. Neither the total length nor its product is an extra hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-central-interval-length"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.central_interval_length"), H("central_interval_length"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The lengths of the nested central intervals add to m(m+1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-central-half-sum-mod-four"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.central_half_sum_mod_four"), H("central_half_sum_mod_four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The sum of the central half-interval quotients modulo two, kept integrally modulo four. This supplies the parity correction in both energy arguments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-evenb-square-sum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.evenB_square_sum"), H("evenB_square_sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Symmetry of the even quotient vector, including both zero endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-evenb-add-central"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.evenB_add_central"), H("evenB_add_central"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The even quotient differs from the central quotient by a negative prefix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-twice-prefix-sum-mod-four"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.twice_prefix_sum_mod_four"), H("twice_prefix_sum_mod_four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The sum of prefixes has the parity of the corresponding triangular number."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprefixparity-square-sum-mod-two"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity.square_sum_mod_two"), H("square_sum_mod_two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Squaring an integer preserves its parity, also under finite summation."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixEnergy")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticSignProducts"))]));
}
