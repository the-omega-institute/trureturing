using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class ClassCAffineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/ClassCAffine.";
    private static readonly LibraryNoteRef PatternSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Position multiplicities give an integer affine invariant and both natural class-C continuation recurrences.",
        H("Class-C Affine Continuation and Recurrences"),
        Blocks(
            Paragraph(Text("Every state is the existing coherent formal State: a finite word p of unused and seen sites, a natural slack s at least one, and a Boolean flag with only the implication that a true flag requires a final S. False-flag words ending in S and all coherent unreachable states are included. The path count is the existing cardinality phi, with labelled old positions and labelled new choices. No recurrence defines a replacement count.")),
            Node("a", "Actual lower-state count",
                "For every natural depth r, positive slack s and natural k, a r s k is phi r at the actual lowerState consisting of k unused sites with false flag. The existing b is phi at the single seen site with true flag. At depth zero both are one because the delivered Path type is Unit. The empty lower-state site word is a formal state, whereas the empty native inversion sequence is handled separately by the native count theorem.", DescribeRole.Definition),
            Node("profile", "A sum over all site positions",
                "For an integer function f, the profile sums f of the number of unused sites strictly to the right of each position. Its recursive first term uses the unused count of the entire tail. Equal suffix counts retain all occurrences. Appending a block of t unused sites and a final S shifts every old suffix count by t, adds the t new unused contributions with exponents t minus one through zero, and adds a separate final-S contribution at exponent zero.", DescribeRole.Definition),
            Node("continuation_affine", "Universal integer affine invariant",
                "For every depth r and every coherent q=(p,s,h), cast phi to the integers. It equals a(r,s,0), plus b(r,s)-a(r,s,1) when h is true and zero when h is false, plus the sum over every position i of a(r,s,k_i+1)-a(r,s,k_i), where k_i counts unused sites strictly after i. The flag coefficient is signed; no positivity premise is imposed on it. The proof first establishes the existence of three affine coefficient families by induction on arbitrary depth, simultaneously for every positive slack and coherent word. The actual first-choice partition supplies the induction: old positions contribute actual lower counts, except for the unique last seen repeat when h is true; every new label uses the smaller-depth affine identity and the positional append transformation. Only after closure, the empty, all-unused and single-seen states identify the constant, adjacent-difference and flag coefficients. Neither target recurrence is used in that induction.", DescribeRole.Theorem),
            Paragraph(Text("Evaluating the affine identity on an unused block of length m followed by S gives a(r,s,m)+b(r,s)-a(r,s,0). Evaluating it on S followed by t unused sites and another S gives a(r,s,t+1)+b(r,s)-a(r,s,0). The two S positions remain separate when t is zero. The explicit empty-to-repeat path complement proves a(r,s,0) at most b(r,s), so each displayed integer expression agrees with the left-associated natural expression a+b-a0 and with a+(b-a0).")),
            Node("a_recurrence", "Original lower-count recurrence",
                "For all natural r,k and s at least one, a(r+1,s,k) is the sum of a(r,s+1,i) for i from zero to k minus one, plus the sum over the original j from one through s of a(r,s-j+1,k+j-1)+b(r,s-j+1)-a(r,s-j+1,0). The finite subtype of the closed interval one through s is the original j index. Its explicit equivalence with Fin s sends t to t+1. Old positions have each suffix-unused exponent exactly once in reverse order; new children are unused blocks followed by S, so the affine evaluation supplies their counts. The natural cast uses the proved empty-to-repeat inequality, preserving the displayed subtraction order.", DescribeRole.Theorem),
            Node("b_recurrence", "Original repeat-count recurrence",
                "For every natural r and s at least one, b(r+1,s) is b(r,s+1) plus the sum over original j from one through s of a(r,s-j+1,j)+b(r,s-j+1)-a(r,s-j+1,0). The single old site repeats with increased slack. Each new child has the initial seen site, j minus one unused sites and a final seen site. Its affine evaluation gives exactly the summand, and the explicit complement justifies natural subtraction. At s equal to one there is one new index, j equal to one; at j equal to s the child slack is one. At k equal to zero the lower recurrence has no old summands. At r equal to zero the defining singleton path counts supply the initial values.", DescribeRole.Theorem),
            Paragraph(Text("The existing extensionEquiv applies to every actual valid nonempty Prefix and every continuation depth. Its cardinality theorem identifies phi of that prefix's state with the actual numeric suffix count. The existing native_avoider_counts separately gives one native empty word and, at length n+1, b(n,1) from the root prefix consisting of zero. Combining those established correspondences with the universal affine and recurrence statements preserves native inversion bounds and the ranked C-pattern exclusions. No realization theorem for every formal state is assumed. The full class-A/B equality, a formal A-to-C bridge and the wider generating-series questions are outside these results."))),
        []));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("inversionseq-classcaffine-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(PatternSource), Blocks(Paragraph(Text(prose))), role);
}
