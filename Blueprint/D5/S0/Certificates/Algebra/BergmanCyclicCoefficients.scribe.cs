using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanCyclicCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact powers and the field criterion in the two cyclic contracted algebras.",
        H("Cyclic contracted-algebra coefficients"),
        Blocks(
            Node("combination", "The actual generator span", "combination",
                "The vector is the sum of a(i) times the basis image of generator i in "
                + "the original contracted Finsupp algebra of Model n q. Both Boolean "
                + "presentations use this same construction. No constant basis element "
                + "or identity is introduced.", DescribeRole.Definition),
            Node("coefficients", "Complete terminal coefficients", "terminal_coefficients",
                "For every positive n, every field F, both presentations and arbitrary "
                + "a,b,c in F, the nth power of ax+by+cz is exactly "
                + "((a+b)^n-b^n) times terminal 0, plus ((b+c)^n-c^n) times terminal 1, "
                + "plus ((c+a)^n-a^n) times terminal 2. This equality excludes every "
                + "other support coordinate. The proof expands actual products of "
                + "basis images, reduces their monomial multisets by normal_mul, "
                + "and evaluates the two-letter and one-letter word filters. "
                + "Unitization is used only to apply the pinned finite sum-power theorem; "
                + "the result is an identity in the original nonunital algebra. "
                + "positivePower v k always means k+1 factors.", DescribeRole.Theorem),
            Node("witness", "Every positive multiple of six", "root_witness",
                "For every positive n divisible by six and every primitive cube root "
                + "omega in F, the actual vector x+omega y+omega^2 z belongs to the "
                + "three-generator span, is nonzero, and has nth power zero, for either "
                + "presentation. The coefficient of x is one and the three generator "
                + "basis images are distinct for n at least two. The geometric sum "
                + "1+omega+omega^2=0, evenness of n and divisibility by three cancel "
                + "all terminal coefficients. This applies in particular over every "
                + "characteristic-zero field containing such a root.", DescribeRole.Theorem),
            Node("field", "The exact sixth-power field criterion", "sixth_power_criterion",
                "For every characteristic-zero field and either n=6 presentation, "
                + "a nonzero vector of the actual three-generator span has sixth power "
                + "zero if and only if the field contains a primitive cube root. "
                + "A nonzero cancellation has all three generator coefficients nonzero. "
                + "The ratios (a+b)/b, (b+c)/c, (c+a)/a are sixth roots unequal to one. "
                + "If there is no primitive cube root, factoring X^6-1 forces all three "
                + "ratios to be minus one; the resulting equations give 9a=0, a "
                + "contradiction in characteristic zero.", DescribeRole.Theorem),
            Node("pairs", "All three actual two-generator spans", "pair_span_nonvanishing",
                "For every n at least two, every field and either presentation, choose "
                + "any one of the three generators to omit. Every nonzero vector in the "
                + "span of the other two basis images has nonzero nth power. A coordinate "
                + "functional vanishes on that span, and the terminal coefficient "
                + "identities then force the other two coefficients to vanish if the "
                + "power vanishes. In particular this proves all three n=6 assertions.",
                DescribeRole.Theorem),
            Paragraph(Text("For these two n=6 presentations the criterion rules out "
                + "cancellation over Q and R and permits it over Q(omega) and C. "
                + "The application uses the usual absence of nontrivial cube roots in "
                + "ordered fields and the primitive cube roots in those extensions. "
                + "It makes no obstruction claim for other rational semigroups. The "
                + "original Question-15 partition remains distinct from both cyclic "
                + "presentations. No general Question-11 or characteristic-p Eggert "
                + "conclusion follows here. The related residue-class binomial "
                + "identities and root-of-unity filtering are prior mathematics, "
                + "including Benjamin and Scott, Theorem 1.1 and its proof. The "
                + "present statements concern the specified semigroups and algebras.")))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
