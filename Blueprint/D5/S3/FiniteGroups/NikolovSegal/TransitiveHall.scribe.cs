using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class TransitiveHallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree counts, actual periodic orbits and simultaneous Hall choices give consecutive good generator intervals.",
        H("Hall interval selection on actual permutation cycles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-finite-degree-matching"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_degree_matching"),
                H("finite degree matching"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite sets W and M, a positive q and neighbor sets t(w), assume every m belongs to at most q neighbor sets and every t(w) has at least q members. There is an injective choice f from W to M with f(w) in t(w). Counting incidence fibers establishes the Hall inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-finite-cycle-incidence-matching"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cycle_incidence_matching"),
                H("finite cycle incidence matching"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite cycle-incidence assumptions give an injective choice of a generator and cycle for every representative. Cycle sizes at most q bound one incidence degree; sufficiently many good generators supply the other degree. The conclusion keeps membership and the actual cycle label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-consecutiveinterval"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.ConsecutiveInterval"),
                H("ConsecutiveInterval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A subset X of Fin m is consecutive when every index between two members also belongs to X. No commutativity of the group products is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-consecutive-block-family"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.consecutive_block_family"),
                H("consecutive block family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, D and M with M times D times (q plus D) at most m, construct M times D pairwise disjoint consecutive blocks, each with q plus D indices, in increasing generator order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-fixedchoice"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.fixedChoice"),
                H("fixedChoice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a representative and a generator block, fixedChoice retains the indices declared good at that representative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-badchoice"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.badChoice"),
                H("badChoice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a representative and a generator block, badChoice retains the complementary indices, where good fails."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-prefixpiece"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.prefixPiece"),
                H("prefixPiece"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected prefix piece is the consecutive portion determined by a good block and the bad-index prefix count. Its defining filters retain both generator membership and the required prefix condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-finite-cover-pigeonhole"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cover_pigeonhole"),
                H("finite cover pigeonhole"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a finite set has at least M times D members and is covered by D subsets, with M and D positive, one covering subset has at least M members. The count is made on the common finite set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-lemma10-3-repeated-matching"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_repeated_matching"),
                H("lemma10 3 repeated matching"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the explicit cycle, good-incidence and disjoint-block hypotheses, repeated Hall choices select the required number of generator-cycle pairs for every representative while retaining their independence across representatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-lemma10-3-interval-selection"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection"),
                H("lemma10 3 interval selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the supplied disjoint consecutive blocks and cycle-incidence bounds, select a prefix piece and M good indices at every representative. The selected piece is consecutive, and simultaneous choices preserve independence of the selected generator-cycle pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-lemma10-3-interval-selection-from-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_from_bound"),
                H("lemma10 3 interval selection from bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The numerical length bound and positive q, D and M provide the block family used by interval selection. All cycle and bad-choice hypotheses remain explicit; the conclusion retains M selected indices, the fixed interval and simultaneous cycle independence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-transitivehall-lemma10-3-interval-selection-actual"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_actual"),
                H("lemma10 3 interval selection actual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the actual periodic orbits of the permutations rather than abstract cycle sets. Positive q and good q-periodicity supply the minimal-period and cycle-cardinality laws. The bound of fewer than D bad indices at each injectively chosen representative and the length bound produce M good indices in a consecutive fixed prefix piece, with distinct actual cycles whenever selected pairs share a generator."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.")))));
}
