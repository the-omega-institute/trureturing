using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Hypergraphs;

internal sealed class FiniteFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/Hypergraphs/FiniteFiber.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite uniform coordinate fibres and disjoint coordinate-block averages.",
        H("Finite coordinate fibres and their exact averages"),
        Blocks(
            Paragraph(Text("A finite uniform mean is a sum " +
                "divided by the cardinality of its finite domain, with that cardinality cast to the " +
                "scalar field. All restrictions below retain the actual coordinate values.")),
            Node("block_average_product", "Disjoint coordinate blocks factor a uniform average",
                "Let ι and J be arbitrary finite types, with decidable equality on ι. Let β:ι→Type " +
                "have a nonempty finite fibre β(i) for every i. Let D:J→Finset ι satisfy " +
                "Disjoint(D(j),D(k)) whenever j≠k. For every real-valued family " +
                "F_j:(Π i∈D(j),β(i))→ℝ, the mean over all o:Π i:ι,β(i) of " +
                "Π j:J F_j(o restricted to D(j)) equals the product over j of the mean of F_j " +
                "over its whole block choice space. Coordinates outside every D(j) are allowed; " +
                "their multiplicity cancels in the normalized average. Empty J and empty blocks " +
                "are not excluded. No independence premise beyond the actual uniform product " +
                "choice space and disjoint coordinate supports is imposed."),
            Node("two_block_event_average", "An exact two-block event average",
                "Let ι have decidable equality, not necessarily be finite. Every β(i) is a nonempty " +
                "finite type with decidable equality. Let L,R:Finset ι be disjoint, and choose " +
                "u:Π i∈L,β(i) and v:Π i∈R,β(i). For arbitrary real A,B,z, assume A is exactly " +
                "the uniform mean of the indicator that all L choices differ from u, and B is " +
                "exactly the uniform mean of the indicator that all R choices differ from v. " +
                "Over the full choice space on L∪R, average z when all L choices avoid u and " +
                "not all R choices avoid v, and average 1 otherwise. The result is exactly " +
                "1−A(1−B)+A(1−B)z. Thus the event requires at least one R hit, not all R hits. " +
                "The input values A and B are constrained by the two stated actual counting equalities."),
            Node("double_uniform_mean_norm_le", "Averaging bounds for complex fibre means",
                "For arbitrary nonempty finite types A and B, f:A→B→ℂ and W:A→B→ℝ, assume " +
                "for every a:A and b:B that the norm of the uniform B-mean of f(a,·) is at most W(a,b). " +
                "Then the norm of the uniform A×B-mean of f is at most the uniform A×B-mean of W. " +
                "W need not be independent of or constant in its second argument. The hypothesis " +
                "holds for every b; it is not merely a bound for one selected representative."),
            Definition("selectedChoiceEquiv", "Dependent choices are exactly valid orientations",
                "For an arbitrary finite index type ι with decidable equality, any type V with " +
                "decidable equality, and E:ι→Finset V, this is an equivalence from Π i:ι,↥(E(i)) " +
                "to ↥(Fintype.piFinset E). The forward map forgets each coordinate's membership " +
                "proof and retains the same V-valued function. The inverse recovers its coordinate " +
                "membership proofs. Neither nonemptiness nor constant edge cardinality is required."),
            Definition("splitCompletion", "Complete the revealed and selected coordinates",
                "For the same ι,V,E and any S:Finset ι, take a:Π i∉S,↥(E(i)) and " +
                "b:Π i∈S,↥(E(i)). The returned complete dependent choice uses b(i) when i∈S " +
                "and a(i) otherwise. Its value lies in E(i) at every coordinate."),
            Definition("splitChoiceEquiv", "The revealed-selected product equivalence",
                "For the same ι,V,E,S, this equivalence maps Π i:ι,↥(E(i)) to " +
                "(Π i∉S,↥(E(i))) × (Π i∈S,↥(E(i))). The complement or revealed choices " +
                "are the first component; selected choices are the second. Its inverse is " +
                "the completion map with this same order of arguments."),
            Definition("splitRevealedImage", "Vertices seen in the revealed coordinates",
                "For the same ι,V,E,S and revealed assignment a:Π i∉S,↥(E(i)), " +
                "this finite set is Finset.univ.image (fun i => (a i).val), with the index " +
                "ranging over the subtype of coordinates outside S. Repeated vertices count once."),
            Node("split_fiber_average", "The characteristic generating function of an actual fibre",
                "Let ι be finite with decidable equality and let V have decidable equality. " +
                "Let E:ι→Finset V and S:Finset ι. Assume E(i) and E(j) are disjoint for " +
                "every two distinct selected coordinates i,j∈S. Let r:ℕ be positive and assume " +
                "|E(i)|=r for every i:ι, including revealed coordinates. Fix any revealed " +
                "assignment a:Π i∉S,↥(E(i)) and any complex z. Put O=splitRevealedImage E S a " +
                "and k_i=|E(i)∖O|. Average exp(z times the cardinality of the image of " +
                "splitCompletion E S a b) over every selected assignment b:Π i∈S,↥(E(i)). " +
                "The exact result is exp(z|O|) times Π i∈S (1−k_i/r+(k_i/r)exp(z)), " +
                "where every count is cast to ℂ. The normalization is the cardinality of " +
                "the entire selected-choice space. No restriction to imaginary z is made; " +
                "empty S is permitted. The k_i are actual set-difference cardinalities, " +
                "not free Bernoulli parameters or an assumed conditional-law decomposition."))));

    private static DocumentBlock Node(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("circular-finite-fiber-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("circular-finite-fiber-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
