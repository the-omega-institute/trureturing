using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanDirectionalCoprimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric line divisibility and the one-direction periodizer implication.",
        H("KhetanDirectionalCoprimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("only-line-direction"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.OnlyLineDirection"),
                H("Literal restriction on the line factors of the original polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex Laurent polynomial P on the integer lattice and a direction u, every nonzero lattice direction v and every nonzero nonunit one-variable complex Laurent polynomial A are tested using the existing lineLaurent embedding. If lineLaurent v A divides P in the original lattice ring, the determinant of u and v must vanish. This definition contains only geometric line divisibility; it has no localized coprimality, eliminant, or irreducibility clause. Nonzero scalar monomials are excluded by the nonunit condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("transverse-difference-coprime"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.transverse_difference_coprime"),
                H("Derive localized coprimality from the geometric restriction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be any complex Laurent polynomial on the integer lattice, let u have coprime integer coordinates, and assume OnlyLineDirection P u. For every integer vector v with nonzero determinant against u, the images of P and differenceFilter v under primitiveLaurentCoordinates followed by coefficient localization to the fraction field of the longitudinal Laurent ring are coprime. No coprimality, irreducibility, eliminant, pairwise nonparallel condition, or low-complexity condition is an assumption.")),
                    Paragraph(Text("The transverse exponent and longitudinal exponent are divided by their integer gcd. The scalar polynomial X to that gcd minus one splits over the complex field. Each root is nonzero. Each resulting primitive binomial is normalized to a monic polynomial. Its irreducibility uses KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime, including even and composite transverse exponents. The coefficient fraction field embeds in the rational-function field through Laurent evaluation; the nonzero constant term has the required signed integer degree.")),
                    Paragraph(Text("If this monic binomial divides a shifted polynomial representative of localized P, Mathlib Polynomial.map_dvd_map descends the division to the longitudinal Laurent coefficient domain. Mapping back to Laurent polynomials and removing the invertible shift gives a literal lineLaurent divisor of the original P. Its direction has positive transverse coordinate, contradicting the geometric restriction. Polynomial Bezout coprimality then maps into the outer Laurent ring. This argument does not require a general Laurent UFD or Gauss-lemma descent framework."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transverse-product-coprime"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.transverse_product_coprime"),
                H("Combine all transverse supplier factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P, primitive u, and OnlyLineDirection P u as above, any finite list of vectors transverse to u gives a product of differenceFilter factors coprime to P after the same coordinate map and coefficient localization. The list may be empty, may contain repetitions, and may contain mutually parallel vectors. The single-factor theorem supplies the coprimality used by the product induction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-direction-periodic"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.one_direction_periodic"),
                H("Use the derived coprimality on the original configuration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let h be a finite-range complex configuration, u a primitive integer direction, and P a Laurent periodizer acting on h as a constant configuration. Assume OnlyLineDirection P u and that a nonzero one-variable Laurent factor in direction u, multiplied by a finite product of transverse differences, annihilates h. Then h has a nonzero global period. The geometric coprimality theorem supplies clear_laurent_bezout, and its cleared identity feeds cleared_bezout_periodic. Rational functions are used to clear the Bezout identity before the resulting genuine Laurent operator acts on h."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-one-direction-periodizer-periodic"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.integer_one_direction_periodizer_periodic"),
                H("Complete one-direction implication for an integer periodizer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let h be an integer configuration with finite range, let P be a nonzero integer Laurent polynomial whose action on h is an integer constant, and let u have coprime integer coordinates. Assume OnlyLineDirection for the complex coefficient image of P and u. Then the given h itself has a nonzero global period. The difference-product annihilator and its split into longitudinal and transverse factors are derived from this same periodizer and configuration. Neither a pre-existing line annihilator nor a localized coprimality assertion is assumed.")),
                    Paragraph(Text("The integer product-difference supplier is reused from KhetanOneDirectionPeriodizer and KhetanAnnihilator, whose pinned source is boonsuan/nivat at revision 4e3614024227acd273c3e8ab41df92c2709e5ab0 and whose MIT attribution is retained there. No low-complexity theorem is used. An injective integer-to-complex alphabet map transfers the resulting period back to h. This is the one-direction branch; it does not assert that every full-span six-cell mask satisfies the line-factor restriction or settle the remaining branch reduction for the full Khetan question."))),
                DescribeRole.Theorem))));
}
