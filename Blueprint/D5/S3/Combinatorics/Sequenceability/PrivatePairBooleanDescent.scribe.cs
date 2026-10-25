using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;
internal sealed class PrivatePairBooleanDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Boolean coverage descent at a private pair",
        H("Exact Boolean coverage descent at a private pair"), Blocks(
        Describe.Lean(DescribeId.Create("main-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.private_pair_exact_boolean_descent"),
            H("A private pair preserves every reduced permutation"),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("M is an integer submodule of functions on the unchanged original indices. "
                + "Complete M E consists of all nonempty proper subsets of the finite original ground set E whose coefficient-one Boolean rows lie in M. "
                + "Covers quantifies over every duplicate-free literal list enumerating E, with an actual nonempty proper contiguous interval. "
                + "Minimal is inclusion minimality in that complete family. Only the selected support S has cardinality at least three; "
                + "the other minimal supports can have arbitrary cardinalities. The distinct original indices u,v lie in S and in no other minimal member."))),
            DescribeRole.Theorem),
        Paragraph(Text("For a row A containing a private index, choose a minimal nonempty Boolean row B inside A. "
            + "If B contains that index, privacy identifies B with S. Otherwise subtract its actual Boolean row and recurse on A minus B. "
            + "The strict finite descent proves S is contained in A. Thus every complete row meeting u or v contains u,v and an actual retained x in S minus {u,v}. "
            + "All larger mixed rows remain in scope.")),
        Paragraph(Text("Write Y = E minus {u,v}. For each given reduced order b, split on actual membership of row Y in M. "
            + "If it is absent, apply original coverage to (u,b,v). A covering row meeting the deleted pair contains both endpoints and is full, a contradiction. "
            + "An avoiding row is an interval of b, and cannot be full Y by the membership split.")),
        Paragraph(Text("If row Y belongs to M, rotate the given b just after x, obtaining (c1,...,x), and apply original coverage to (u,c1,v,c2,...,x). "
            + "A row meeting the pair contains both endpoints u,x and is full. An avoiding row lies inside one of two proper pieces. "
            + "The existing ZeroTotalCircleGood.rotated_two_runs supplier makes either that run or its complement an interval of the SAME original b. "
            + "The exact identity row(complement) = row(Y) - row(run) gives membership in M. Both witnesses are nonempty and proper; "
            + "full Y is excluded even in this second case. The reduced length two boundary is included.")),
        Paragraph(Text("The reducedSpan definition is exactly the integer span of ALL proper reduced Boolean rows whose extension by zero belongs to M. "
            + "Its image under embed lies in M. Conversely every nonempty proper reduced Boolean row with image in M is a generator, "
            + "so this is its complete proper Boolean family. Extension sends a unit and a difference to the same coefficient-one original coordinate vectors. "
            + "No equality with an intersection lattice, rational saturation, division, original total-sum or torsion assumption is asserted.")),
        Paragraph(Text("For the original source family H, instantiate M with Submodule.span over integer Boolean rows of H. "
            + "Original H coverage implies Covers because each source row is a generator. Each output image in M therefore has finite ORIGINAL-H integer coefficients, "
            + "by Mathlib's Submodule.mem_span_image_finset_iff_exists_fun. For an original interval source A, the direct witness has its original generator coefficients; "
            + "the complement witness subtracts those coefficients from an actual certificate for row Y. Finite linear combinations compose these coefficients. "
            + "This exact application is compiled transiently rather than retained as a named binding theorem.")),
        Paragraph(Text("This is a repository-derived descent lemma. The unrestricted original connector, Good and adaptive merge statements remain open. "
            + "No forest constructor or literature-priority claim is part of this delivery.")) )));
}
