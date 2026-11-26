using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class OrderedSlaterPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slater determinant marginals at an ordered cut",
        H("Slater determinant marginals at an ordered cut"),
        Blocks(
            Entry("prefix_product_spectrum", "The full product spectrum at an ordered prefix",
                "For a matrix with orthonormal columns on a consecutive site order, the marginal on the first m sites has the complete product spectrum determined by the retained compression. The characteristic polynomial includes all occupation labels and all multiplicities.",
                StatementSource.WithoutFormula(), DescribeRole.Theorem),
            Theorem("universal_cut_product_iff", "Cut classification for the full Slater product spectrum", CutCriterion(),
                "At a prefix, a unitary change of basis on the retained site rows acts by the corresponding ordered minors in each retained particle-number sector. These sector matrices are unitary by Cauchy–Binet, so the full marginal characteristic polynomial is invariant. Diagonalize the retained compression. The weighted Cauchy–Binet formula for determinant contractions then gives the diagonal occupation weights. Equality of the compression characteristic polynomials allows any relabeling of the mode values, including repeated and zero eigenvalues. For a cut without four alternating sites, the fixed-occupation shuffle and the stable ordering of the sides reduce the problem to the prefix. At either alternating order, two occupied orbitals give two ordinary marginal eigenvalues of one half while the product spectrum has a single nonzero eigenvalue of one."))));

    private static DocumentBlock Theorem(string name, string title, Formula statement, string prose) =>
        Entry(name, title, prose, StatementSource.FromAuthor(Disp(statement)), DescribeRole.Theorem);

    private static DocumentBlock Entry(string name, string title, string prose, StatementSource source,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("ordered-slater-prefix-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), source, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula N(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Named(name), Open, Join(args), Close);
    private static Formula Join(Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var arg in args)
        {
            if (parts.Count > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(arg);
        }
        return Seq(parts.ToArray());
    }

    private static Formula Typed(string name, Formula type) => Seq(N(name), Colon, Sp, type);
    private static Formula Sites => Seq(
        Forall, Sp, Iota, Colon, Sp, Named("Type"), Comma, Sp,
        OpenBracket, Call("LinearOrder", Iota), CloseBracket, Sp,
        OpenBracket, Call("Fintype", Iota), CloseBracket, Comma, Sp,
        Typed("I", Call("Set", Iota)), Comma);

    private static Formula Complex => Seq(Mathbb, Grp(N("C")));
    private static Formula Naturals => Seq(Mathbb, Grp(N("N")));
    private static Formula V => N("V");
    private static Formula I => N("I");
    private static Formula Identity(Formula matrix) => Seq(matrix, Caret, Grp(Star), matrix, Eq, D(1));
    private static Formula Alternates => Call("Alternates", I);
    private static Formula OrbitalMatrix(Formula sites, Formula k) =>
        Call("Matrix", sites, Call("Fin", k), Complex);

    private static Formula CutCriterion()
    {
        var k = N("k");
        return new Formula.Aligned([
            Sites,
            Seq(Neg, Alternates, Sp, Iff, Sp, Forall, Sp, k, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Typed("V", OrbitalMatrix(Iota, k)), Comma),
            Seq(Identity(V), Sp, Longrightarrow, Sp, Call("HasProductSpectrum", I, V))
        ]);
    }
}
