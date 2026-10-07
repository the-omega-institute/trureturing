using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SmallTwistedGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twisted values generate a noncommutative simple group.",
        H("Twisted values generate a noncommutative simple group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-smalltwistedgeneration-ordinary-from-twisted"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SmallTwistedGeneration.ordinary_from_twisted"),
                H("ordinary from twisted"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three actual twisted values express an ordinary commutator, with arbitrary automorphisms a and b and without a coverage oracle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-smalltwistedgeneration-noncommutative-simple-commutator-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SmallTwistedGeneration.noncommutative_simple_commutator_top"),
                H("noncommutative simple commutator top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real generated commutator subgroup of a noncommutative simple group is the whole group."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-smalltwistedgeneration-twisted-closure-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SmallTwistedGeneration.twisted_closure_top"),
                H("twisted closure top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual twisted value set generates the whole noncommutative simple group."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
