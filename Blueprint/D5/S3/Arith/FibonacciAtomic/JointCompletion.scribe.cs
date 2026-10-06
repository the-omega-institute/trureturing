using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class JointCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/JointCompletion.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula And(params Formula[] formulas)
    {
        var parts = new List<Formula>();
        foreach (var formula in formulas)
        {
            if (parts.Count > 0) parts.Add(Seq(Sp, Land, Sp));
            parts.Add(Par(formula));
        }
        return Seq(parts.ToArray());
    }
    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("joint-completion-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite legal Fibonacci sources complete to the product of legal infinite addresses and two profinite integer coordinates.",
        H("Joint Source Completion"),
        Blocks(
            Paragraph(Text("Omega is the space of infinite Boolean addresses without adjacent ones. "
                + "The profinite integers are the existing compatible residue families over all "
                + "positive moduli, and K is Omega times two copies of that space. D consists "
                + "of the eventually zero legal addresses. X(L) is the existing space of legal "
                + "words of length L. The index m denotes the positive modulus m+1, so every "
                + "positive modulus and the empty prefix are included.")),
            Definition("jointObservation", "Finite joint observations",
                "Q(k)(L,m) consists of the low prefix P(L,omega) and both residue coordinates "
                + "of z modulo m+1, for k=(omega,z) in K."),
            Definition("sourceGraph", "Actual finite-source graph",
                "gamma(b) pairs the actual address b with the two profinite residue families "
                + "of its existing Fibonacci sourceComposition. Its range is the graph Gamma; "
                + "the two coordinates come from the same finite source."),
            Definition("compatibleObservations", "Bonding conditions",
                "A joint reading family q is compatible when increasing the prefix length "
                + "and replacing a modulus by a multiple preserves every lower bit and reduces "
                + "each residue to the corresponding lower-modulus reading. These are precisely "
                + "the prefix-truncation and modular-reduction bonding maps."),
            Definition("sourceUniformity", "Finite-observation uniform structure",
                "The source uniform structure is the infimum of the pullbacks of the finite "
                + "joint observation spaces. Thus agreement means simultaneous equality of a "
                + "finite low prefix and the two modular Fibonacci-composition coordinates."))));
}
