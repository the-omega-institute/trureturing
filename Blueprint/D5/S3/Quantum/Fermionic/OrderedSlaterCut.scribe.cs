using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class OrderedSlaterCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/OrderedSlaterCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slater determinant marginals at an ordered cut",
        H("Slater determinant marginals at an ordered cut"),
        Blocks(
            Paragraph(Text("A finite linearly ordered set of sites is partitioned into a retained set and its complement. Both sides can be empty. The matrix of occupied orbitals has one column per particle. Each side keeps its full occupation carrier, including occupation labels with zero amplitude.")),
            Definition("Occupation", "Occupation labels",
                "An occupation label is a finite subset of the indicated side."),
            Definition("retainedRows", "Retained one-particle rows",
                "Restrict the orbital matrix to the retained site rows and keep the original particle columns."),
            Definition("orderedCut", "Amplitudes in the original site order",
                "Join the two occupied subsets and use their increasing enumeration for the rows of the determinant. The entry is zero when the joined subset has a different size from the particle number."),
            Definition("groupedCut", "Amplitudes in the order grouped by side",
                "List the occupied rows on the retained side before the occupied rows on the traced side. The order within each side is increasing. The same particle number condition determines the zero entries."),
            Theorem("alternating_cut_obstruction", "The two-particle witness at an alternating cut", AlternatingWitness(),
                "For either orientation of a four-site alternation, take one normalized two-site orbital on each side and leave every other site empty. The orbitals are orthogonal. The compression has a single nonzero eigenvalue of one. The grouped marginal has a single nonzero eigenvalue of one. The original-order marginal has two nonzero eigenvalues of one half, and the two remaining polynomial factors are powers of X with the exponents specified by the full carriers."),
            Definition("bernoulliWeight", "Weight of an occupation in the product spectrum",
                "For each retained site label, use the supplied mode value when that label is occupied and one minus that value otherwise. Multiply over all labels."),
            Definition("HasProductSpectrum", "The complete product-spectrum property",
                "For every labeling that factors the characteristic polynomial of the retained one-particle compression, the original-order determinant marginal has the characteristic polynomial with one factor for every occupation weight. This preserves repeated and zero eigenvalues."),
            Theorem("universal_cut_product_iff_of_prefix", "Reduction of the cut classification to the ordered-prefix formula", CutCriterion(),
                "Assume the product-spectrum property for every prefix and every column-orthonormal orbital matrix on the consecutive order. At an arbitrary cut with no four alternating sites, the occupied permutation contributes the cross-inversion sign. The fixed-occupation shuffle theorem preserves the marginal characteristic polynomial. The stable ordering of the two sides then transports the grouped marginal, the retained compression and each occupation weight to the prefix formula. If four sites alternate, the two-particle witness has a rank-one compression with a single nonzero eigenvalue of one. Its occupation product spectrum is concentrated at one weight of one, so the original-order marginal violates the formula."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Entry(name, title, prose, StatementSource.WithoutFormula(), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula statement, string prose) =>
        Entry(name, title, prose, StatementSource.FromAuthor(Disp(statement)), DescribeRole.Theorem);

    private static DocumentBlock Entry(string name, string title, string prose, StatementSource source,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("ordered-slater-cut-" + name.Replace('_', '-').ToLowerInvariant()),
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

    private static Formula Parens(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(string name, Formula type) => Seq(N(name), Colon, Sp, type);
    private static Formula Sites => Seq(
        Forall, Sp, Iota, Colon, Sp, Named("Type"), Comma, Sp,
        OpenBracket, Call("LinearOrder", Iota), CloseBracket, Sp,
        OpenBracket, Call("Fintype", Iota), CloseBracket, Comma, Sp,
        Typed("I", Call("Set", Iota)), Comma);

    private static Formula Complex => Seq(Mathbb, Grp(N("C")));
    private static Formula Naturals => Seq(Mathbb, Grp(N("N")));
    private static Formula V => N("V");
    private static Formula W => N("W");
    private static Formula I => N("I");
    private static Formula X => N("X");
    private static Formula Identity(Formula matrix) => Seq(matrix, Caret, Grp(Star), matrix, Eq, D(1));
    private static Formula Alternates => Call("Alternates", I);
    private static Formula OrbitalMatrix(Formula sites, Formula k) =>
        Call("Matrix", sites, Call("Fin", k), Complex);
    private static Formula CharpolyOfGram(Formula matrix) =>
        Call("charpoly", Seq(matrix, matrix, Caret, Grp(Star)));
    private static Formula Power(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));

    private static Formula AlternatingWitness()
    {
        var retained = Call("retainedRows", I, V);
        var grouped = Call("groupedCut", I, V);
        var ordered = Call("orderedCut", I, V);
        var occupationCount = Call("card", Call("Occupation", I));
        var factorOne = Parens(Seq(X, Minus, D(1)));
        var factorHalf = Parens(Seq(X, Minus, Call("C", Seq(Frac, Grp(D(1)), Grp(D(2))))));
        return new Formula.Aligned([
            Sites,
            Seq(Alternates, Sp, Longrightarrow, Sp, Exists, Sp,
                Typed("V", OrbitalMatrix(Iota, D(2))), Comma, Sp, Identity(V), Sp, Land),
            Seq(CharpolyOfGram(retained), Sp, Eq, Sp,
                Power(X, Seq(Call("card", I), Minus, D(1))), factorOne, Sp, Land),
            Seq(CharpolyOfGram(grouped), Sp, Eq, Sp,
                Power(X, Seq(occupationCount, Minus, D(1))), factorOne, Sp, Land),
            Seq(CharpolyOfGram(ordered), Sp, Eq, Sp,
                Power(X, Seq(occupationCount, Minus, D(2))), Power(factorHalf, D(2)))
        ]);
    }

    private static Formula CutCriterion()
    {
        var m = N("m");
        var n = N("n");
        var k = N("k");
        var prefix = Seq(OpenBrace, N("i"), Sp, InMacro, Sp, Call("Fin", Seq(m, Plus, n)),
            Sp, Mid, Sp, Call("val", N("i")), Lt, m, CloseBrace);
        return new Formula.Aligned([
            Seq(Open, Forall, Sp, m, Comma, n, Comma, k, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Typed("W", OrbitalMatrix(Call("Fin", Seq(m, Plus, n)), k)), Comma),
            Seq(Identity(W), Sp, Longrightarrow, Sp, Call("HasProductSpectrum", prefix, W), Close, Sp,
                Longrightarrow),
            Sites,
            Seq(Neg, Alternates, Sp, Iff, Sp, Forall, Sp, k, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Typed("V", OrbitalMatrix(Iota, k)), Comma),
            Seq(Identity(V), Sp, Longrightarrow, Sp, Call("HasProductSpectrum", I, V))
        ]);
    }
}
