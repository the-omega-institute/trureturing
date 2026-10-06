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
                + "finite low prefix and the two modular Fibonacci-composition coordinates."),
            Describe.Lean(DescribeId.Create("joint-completion-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Joint compact completion"),
                StatementSource.FromAuthor(And(
                    Seq(Forall, Sp, V("i"), Sp, InMacro, Sp, V("N"), Caret, Grp(Num(2)),
                        Comma, Sp, Call("Surjective", Call("Qgamma", V("i")))),
                    And(Call("UniformEmbedding", V("Q")),
                        Seq(Forall, Sp, V("q"), Comma, Sp, Call("Compatible", V("q")),
                            Sp, Iff, Sp, Exists, Bang, Sp, V("k"), Sp, InMacro, Sp, V("K"),
                            Comma, Sp, Call("Q", V("k")), Sp, Eq, Sp, V("q"))),
                    And(Call("DenseRange", V("gamma")),
                        Seq(Forall, Sp, V("k"), Sp, InMacro, Sp, V("K"), Comma, Sp,
                            Exists, Sp, V("s"), Colon, Sp, V("N"), Sp, To, Sp, V("D"), Comma, Sp,
                            And(Seq(Forall, Sp, V("n"), Comma, Sp,
                                Call("Q", Call("gamma", Call("s", V("n"))), Call("i", V("n"))),
                                Sp, Eq, Sp, Call("Q", V("k"), Call("i", V("n")))),
                                Seq(Call("gamma", Call("s", V("n"))), Sp, To, Sp, V("k"))))),
                    And(Call("Compact", V("K")), Call("UniformEmbedding", V("gamma")),
                        Call("AbstractCompletionOn", V("K"), V("D"), V("UD"), V("gamma"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Q_gamma(i) sends a source b to Q(gamma(b))(i). The pair "
                        + "i(n) is (n,(n+1)!-1), whose second index represents the modulus (n+1)!. "
                        + "The convergence arrow is convergence as n tends to infinity. All "
                        + "uniform embeddings use the product and subspace uniform structures, "
                        + "with each finite residue space discrete and the source structure U_D "
                        + "given by sourceUniformity. AbstractCompletionOn denotes the existence "
                        + "of a mathlib AbstractCompletion of (D,U_D) with underlying space K, "
                        + "the stated product uniform structure, and inclusion gamma.")),
                    Paragraph(Text("The joint observation map is a uniform embedding into the "
                        + "product of finite reading spaces. Its image is exactly the compatible "
                        + "reading families: the j-th bit is recovered from a prefix of length "
                        + "j+1, and each residue is recovered from the empty-prefix reading. "
                        + "Compatibility makes these recovered bits legal and makes both "
                        + "residue families profinite integers. This identifies K with the "
                        + "inverse limit in the product subspace topology.")),
                    Paragraph(Text("For every k, remote vector compensation supplies one finite "
                        + "source at each stage with its first n bits and both residues modulo "
                        + "(n+1)!. Every fixed positive modulus divides all sufficiently large "
                        + "stage moduli, so each fixed residue coordinate is eventually correct. "
                        + "Each fixed bit is also eventually correct. The resulting sources "
                        + "converge to k and prove that the actual graph is dense. Legality and "
                        + "modular compatibility are closed conditions in products of finite "
                        + "discrete spaces. Hence K is compact Hausdorff and complete, and the "
                        + "dense uniform embedding gives its abstract completion structure."))),
                DescribeRole.Theorem))));
}
