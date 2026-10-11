using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIIConjugacyValueConsumptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Conjugacy Value Consumption.",
        H("Type-A Conjugacy Value Consumption"),
        Blocks(
            Paragraph(Text("The exact noncommutative conversion in PartII Section5 equation(4) turns an ordered conjugacy-class word into genuine commutator values. The finite-outer consumer is constructed, and class-product width is supplied by the later explicit supported-factor proof.")),
            Describe.Lean(
                DescribeId.Create("typea-partiiconjugacyvalueconsumption-ordered-conjugacy-commutator-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIConjugacyValueConsumption.ordered_conjugacy_commutator_values"),
                H("ordered conjugacy commutator values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every factor remains a genuine h-commutator value. The witness u_i*h^-i and the final h^-N offset retain increasing, noncommutative order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiconjugacyvalueconsumption-actual-bare-psln-conjugacy-word-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIConjugacyValueConsumption.actual_bare_PSLn_conjugacy_word_values"),
                H("actual bare PSLn conjugacy word values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual Section5 consumption for arbitrary bare PSLn automorphisms, now including F3/F4. one original right correction precedes every genuine class-witness tuple; all unused indices and original q/e remain exact. The proved class-size bound does not supply uniform class product width."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
