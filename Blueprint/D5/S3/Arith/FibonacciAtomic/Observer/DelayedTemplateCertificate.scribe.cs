using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class DelayedTemplateCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One delayed physical probe per original leaf identifies any known finite template.",
        H("Delayed leaf certificates for arbitrary templates"), Blocks(
            Paragraph(Text("The template g is known finite native syntax, while the competitor u ranges over all native finite trees. No equal-shape, equal-size, positive-image or finite-competitor premise is imposed. The common natural epoch N changes physical addresses and expected labels. Every requested address and every expected reply is computed from N and g.")),
            Definition("leafReply", "Literal label reply", "leafReply(true)=alpha and leafReply(false)=beta."),
            Definition("leafBit", "Known frontier label", "leafBit(g,p) tests whether the known template reply is alpha. On its original leaves this is precisely the Boolean leaf label. The beta default outside the original frontier is never used to construct a certificate entry."),
            Definition("leafDelay", "Label-dependent physical delay", "leafDelay(N,b)=N/2+(N%2) times the beta indicator, which is zero for alpha and one for beta."),
            Definition("expected", "Expected delayed leaf", "At even epochs the expected reply is the original leaf label. At odd epochs the expected alpha and beta labels are swapped. Both expected replies are actual leaf labels."),
            Definition("templateQueries", "One query per original leaf", "Map the original leaf list p of g, in left-to-right order, to p followed by rights(leafDelay(N,leafBit(g,p))). The generator inspects only the known template."),
            Definition("templateExpected", "Known expected list", "Map the same original leaf list to expected(N,leafBit(g,p)), preserving exactly the same chronological order as templateQueries."),
            Definition("templateCheck", "Total terminal Boolean output", "Compare the complete supplied reply list with templateExpected. A wrong reply or a wrong list length returns false. This compares finite replies, never unknown source trees."),
            Definition("DelayedMatches", "Unrestricted semantic matching", "For every original leaf p of g, the actual current reply at its generated probe equals the generated expected leaf. The definition quantifies all native competitor trees without a shape promise."),
            Definition("rightTip", "Rightmost original leaf", "A leaf has right-tip depth zero and its own label. Pair(x,y) adds one to the right-tip depth of y and keeps its label. Its physical all-right original address belongs to the complete leaf list."),
            Theorem("delayed_leaf_reflection", "Delayed evidence reflects original leaves", "For all N,g,u, delayed matching implies equality of the original replies of u and g at every original leaf of g. A branch template cannot collapse to a competing leaf. Its rightmost leaf has positive relative depth, so the delayed probe either passes beyond that leaf image or gives the wrong label. In particular, at N=1, pair(alpha,alpha) versus beta is rejected by the right probe returning alpha instead of the expected beta, rather than by an absent reply."),
            Theorem("delayed_template_certificate", "Exact whole-tree identification", "For every N,g,u, DelayedMatches(N,g,u) holds if and only if u=g. The forward direction applies the existing unrestricted zero-delay source_foundation leaf rigidity directly to delayed_leaf_reflection. The reverse direction recursively verifies each actual delayed leaf. Iterated pair preservation is the direct Mathlib Semiconj2 iteration applied to substitution.map_mul."),
            Definition("leafAddressSum", "Original leaf word sum", "leafAddressSum(g) is the sum of the lengths of the original leaf list."),
            Definition("delayedRadius", "Exact maximum generated length", "Map every original leaf p to length(p)+N/2+(N%2) times its beta indicator, and take the maximum with zero as empty-list default. Native sources have at least one leaf, so this is the maximum over the nonempty frontier."),
            Theorem("delayed_template_resources", "Exact three-coordinate resources", "The generated physical query list has no duplicates and length exactly FreeMagma.length(g). Its total address length is leafAddressSum(g)+(N/2) times FreeMagma.length(g)+(N%2) times the beta component of composition(g). Its maximum address length is delayedRadius(N,g). Probe distinctness uses the prefix incomparability of original leaves: two equal extended words would give comparable original leaf prefixes, hence identical leaves. The existing native total and beta leaf counts identify the coefficients."),
            Theorem("delayed_template_service", "Finite full-list checker", "The executable listController terminates with fuel length(templateQueries)+1, recording the actual ordered replies and returning templateCheck. Its output is true exactly when u=g. The chronological number of calls is exactly FreeMagma.length(g); the actual transcript address-length sum and maximum equal the two displayed resources. Full-list checking, including after a mismatch, attains these exact equalities."),
            Paragraph(Text("With a physically lawful original-present prefix a, append a to every generated address and use the original-present transport and appended-readout bridge. The call count stays ell(g); the word sum increases by length(a) times ell(g), and the radius increases by length(a). These are list identities on a nonempty frontier. The original-present premise remains essential; an address born later is not a substitute.")),
            Paragraph(Text("Different ground-binding checks may submit overlapping physical addresses independently. Every occurrence then counts as an additional raw call. This one-probe-per-leaf construction preserves coefficient one in the ground-template part of a stationary whole-row upper bound; using the two-call original decoder per template leaf would not give that coefficient. Finite-cell selection, ground-binding decision, same-register operation and whole-row output are separate constructions. The equalities here assert attainment by this checker, without a minimax or lower-bound claim."))
        )));

    private static DocumentBlock Definition(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("delayedtemplatecertificate-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("delayedtemplatecertificate-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
