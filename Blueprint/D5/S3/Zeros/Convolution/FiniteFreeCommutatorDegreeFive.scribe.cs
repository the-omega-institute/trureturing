using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class FiniteFreeCommutatorDegreeFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite free commutator of any two monic real-rooted quintics has five real roots.",
        H("Finite Free Commutators in Degree Five"),
        Blocks(
            Paragraph(Text(
                "This is the degree-five case of Conjecture 5.3 in Campbell, Morales and Perales, "
                + "arXiv:2502.00254v2. The verified locator scope is Notation 5.1 on printed "
                + "page 19, Conjecture 5.3 and Theorem 5.6 on page 20, and Remark 5.7 on page 21. "
                + "The DOI is 10.3842/SIGMA.2025.108. The source operation is Sym(p) boxtimes_5 "
                + "Sym(q) boxtimes_5 z(5). The additional hypothesis of Theorem 5.6 is not used. "
                + "The bounded literature recheck and implementation provenance are recorded "
                + "in docs/reports/r18-quintic-preregistration.md. No worldwide priority is asserted.")),
            Describe.Lean(
                DescribeId.Create("centered-quintic-sharp-coefficient-bound"),
                DeclarationHandle.Create(Prefix + "centered_quintic_coefficient_bound"),
                H("Sharp coefficient estimate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X^5+uX^3+vX^2+wX+t with five real roots, w is at most 4u^2/15. "
                    + "Sort the roots and express 30 times their fourth moment minus seven "
                    + "times the square of their second moment as a polynomial with 22 "
                    + "nonnegative monomials in consecutive root gaps. Newton identities "
                    + "give the coefficient estimate. Roots (2,2,2,-3,-3) attain equality, "
                    + "with u=-15 and w=60."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("quintic-commutator-source-expansion"),
                DeclarationHandle.Create(Prefix + "centered_expansion"),
                H("Definition-derived coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For centered inputs with cubic coefficients u,U and linear coefficients "
                    + "w,W, the output is X^5-(5uU/6)X^3 "
                    + "+((3u^2+20w)(3U^2+20W)/450)X. Sym, each multiplicative convolution, "
                    + "and z(5)=X^5-(125/6)X^3+(50/9)X are expanded from the frozen definitions. "
                    + "The consumer is centered_factorization."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("centered-quintic-invariant-bounds"),
                DeclarationHandle.Create(Prefix + "centered_quintic_invariant_bounds"),
                H("Rolle and the frozen quartic estimate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplicity-aware Rolle makes p'/5 a real-rooted centered quartic "
                    + "with coefficients 3u/5,2v/5,w/5. The frozen "
                    + "FiniteFreeCommutatorDegreeFour.centered_quartic_invariant_bounds gives "
                    + "u<=0 and 3u^2+20w>=0. The sharp quintic estimate gives the upper bound "
                    + "3u^2+20w<=25u^2/3. These bounds feed the discriminant and factor signs."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("centered-quintic-discriminant-bound"),
                DeclarationHandle.Create(Prefix + "centered_discriminant_bound"),
                H("Discriminant lower bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the squared variable, the discriminant is at least 25u^2U^2/324. "
                    + "An exact remainder identity reduces this inequality to the two "
                    + "input invariant bounds. The consumer is centered_factorization."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("centered-quintic-commutator-factorization"),
                DeclarationHandle.Create(Prefix + "centered_factorization"),
                H("Nonnegative squared roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The output factors as X(X^2-s)(X^2-t) with s,t nonnegative. "
                    + "The construction uses the nonnegative square root of the discriminant "
                    + "and allows it to vanish. The consumer is centered_real_rooted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered-quintic-commutator-real-rooted"),
                DeclarationHandle.Create(Prefix + "centered_real_rooted"),
                H("Five real factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exhibited roots are 0,sqrt(s),-sqrt(s),sqrt(t),-sqrt(t). "
                    + "An equality to a product indexed by Fin(5) retains repeated roots "
                    + "and zero roots. The consumer is real_rooted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quintic-commutator-real-rooted"),
                DeclarationHandle.Create(Prefix + "real_rooted"),
                H("Arbitrary monic quintics"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every monic quintic with five real roots has a coefficient representation "
                    + "X^5+aX^4+uX^3+vX^2+wX+t. Translation by -a/5 centers it and preserves "
                    + "its five real factors. A definition-derived identity proves that Sym "
                    + "is unchanged by translation, so the centered result applies to both "
                    + "arbitrary inputs. Only degree five is concluded; the all-degree "
                    + "conjecture remains outside this module."))), DescribeRole.Theorem))));
}
