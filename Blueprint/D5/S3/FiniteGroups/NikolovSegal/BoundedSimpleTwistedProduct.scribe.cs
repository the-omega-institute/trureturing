using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class BoundedSimpleTwistedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered bounded-small twisted PRODUCT coverage.",
        H("Ordered bounded-small twisted PRODUCT coverage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-boundedsimpletwistedproduct-productrange-full-or-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BoundedSimpleTwistedProduct.productRange_full_or_card"),
                H("productRange full or card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any arbitrary ordered d-tuple of automorphism pairs in a finite noncommutative simple group, the genuine twisted product range is full or has at least d+1 elements. Strict finite-set growth proves the assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-boundedsimpletwistedproduct-twisted-input-of-card-le-succ"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BoundedSimpleTwistedProduct.twisted_input_of_card_le_succ"),
                H("twisted input of card le succ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite noncommutative simple S with Nat.card(S) at most D+1, every ordered D-tuple of genuine automorphism pairs has twisted PRODUCT coverage. No perfectness or coverage oracle is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-boundedsimpletwistedproduct-bounded-small-simple-twisted-input"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/BoundedSimpleTwistedProduct.bounded_small_simple_twisted_input"),
                H("bounded small simple twisted input"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A cardinality cutoff C gives genuine twisted PRODUCT coverage at length C+1."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
