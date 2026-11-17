using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class AdaptiveTwoReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/AdaptiveTwoReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On every fixed finite support of at least three labels, two labeled deletions from the same original oriented circle fail to reconstruct it, even when the second label is chosen deterministically from the first residual.",
        H("Two Adaptive Circular Deletion Readouts"),
        Blocks(
            Paragraph(Text("Let alpha be any type with decidable equality, and let A be a finite set of labels. "
                + "Cycle(alpha) identifies lists under rotation and retains orientation. SupportedCircle(A) is the subtype of cycles C "
                + "with C.Nodup and C.toFinset = A. Thus every label of A occurs exactly once. Labels(A) denotes the subtype "
                + "of labels belonging to A; Function(U,V) denotes functions from U to V.")),
            Paragraph(Text("Fix a first label x in Labels(A). A deterministic policy sigma maps every Cycle(alpha) to Labels(A). "
                + "For an original C, put B = delete(x,C) and z = sigma(B). The definition adaptiveTrace(A,x,sigma)(C) "
                + "retains the ordered tuple (x,B,z,delete(z,C)). Both deletions are readouts of the same original C. "
                + "The second label may equal x, and all residual labels retain their original names. "
                + "A fixed x and sigma already supply every policy for this two-query model, since A and the first label are fixed.")),
            Describe.Lean(DescribeId.Create("no-adaptive-two-reconstruction"),
                DeclarationHandle.Create(Prefix + "no_adaptive_two_reconstruction"),
                H("Two Adaptive Readouts Are Noninjective"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every A of cardinality at least three, every first label x in A, and every deterministic "
                        + "policy sigma from Cycle(alpha) to Labels(A), the full map adaptiveTrace(A,x,sigma) on SupportedCircle(A) "
                        + "is not injective. There are distinct supported original circles with the same first label, first residual, "
                        + "second label, and second residual. This includes every support of cardinality at least four.")),
                    Paragraph(Text("The proof works on every supported first-residual branch B, rather than choosing a label pair "
                        + "before B is known. Write z = sigma(B). If z differs from x, rotate a representative of B to z::R. "
                        + "Then C is the cycle of x::z::R and D is the cycle of x::(R++[z]). Both are nodup with exact support A. "
                        + "Deleting x gives z::R and R++[z], which represent the same oriented cycle B. Deleting z gives x::R in both cases. "
                        + "The bound on A makes R nonempty. If C equaled D, CyclicInsertionGap.anchored_coe_injective at x "
                        + "would give z::R = R++[z]; their first entries would force z to occur in R, contrary to nodup. "
                        + "This is the construction in adjacent_pair_collision.")),
                    Paragraph(Text("If z equals x, choose any label of A.erase(x) and use the same two adjacent insertions. "
                        + "The lemma two_gap_collision retains their distinctness and common first residual. Repeating x then "
                        + "returns B again on both original circles. The lemma adaptive_branch_collision combines these cases "
                        + "for an arbitrary B. Finally, exists_supported_residual supplies B from the toList of A.erase(x). "
                        + "Equality of the two full tuples contradicts injectivity on SupportedCircle(A)."))),
                DescribeRole.Theorem),
            Paragraph(Text("The support restriction on the policy is essential: deleting an ambient label outside A would leave "
                + "the original circle unchanged and reveal it. The model keeps the second deletion on the original circle, "
                + "rather than deleting from the first residual. The proof does not use the paired-deletion fiber classification. "
                + "The positive direction for supports of cardinality at most two remains a separate, unformalized boundary. "
                + "This theorem gives a two-observation obstruction, not a general optimum or a mean-cost bound.")),
            Paragraph(Text("The result is repository-derived from the explicit insertion construction and the existing circular "
                + "deletion API. The verified publisher abstracts of Permutation Reconstruction (DOI 10.37236/1149) and "
                + "Permutation Reconstruction from Minors (DOI 10.37236/1092) describe deletion minors with order-preserving "
                + "renumbering. The verified abstract of Reconstructing Permutations from Cycle Minors (DOI 10.37236/108) "
                + "describes deletion in a permutation's disjoint-cycle decomposition, again reducing larger labels. "
                + "Those abstract-level comparisons do not establish a prior theorem or priority for the exact fixed-label "
                + "adaptive statement here. No literature novelty claim is made.")))));

    private static Formula Statement()
    {
        Formula t = F.Id("alpha"), a = F.Id("A"), x = F.Id("x"), sigma = F.Id("sigma");
        Formula labels = Call("Labels", a);
        Formula policies = Call("Function", Call("Cycle", t), labels);
        Formula conclusion = new Formula.Not(Call("Injective", Call("adaptiveTrace", a, x, sigma)));
        return Disp(All("alpha", Call("Type"), Seq(OpenBracket, Call("DecidableEq", t), CloseBracket, Sp,
            All("A", Call("Finset", t), Imp(Le(D(3), Call("card", a)),
                All("x", labels, All("sigma", policies, conclusion)))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}
