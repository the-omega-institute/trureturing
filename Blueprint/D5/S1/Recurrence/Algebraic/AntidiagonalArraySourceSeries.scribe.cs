using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class AntidiagonalArraySourceSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.";
    private static readonly LibraryNoteRef ArraySource =
        LibraryNoteRef.Create("D5/L/Recurrence/kurkov2025a392095");
    private static readonly LibraryNoteRef SeriesSource =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2003a088713");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The antidiagonal natural array and the normalized rational source series are uniquely determined, and their first-column coefficients agree after a one-step shift.",
        H("Antidiagonal Array and Source Series"),
        Blocks(
            Paragraph(Text(
                "Mikhail Kurkov's A392095 defines the total natural function array: "
                    + "its zeroth row is one and each successor row uses the shifted entry and "
                    + "the finite sum over j from zero through k. The source is the normalized "
                    + "rational power series specified independently by Paul D. Hanna's "
                    + "A088713 equation F(x/F(x))=(1-x)^(-1). "
                    + "All coefficients are indexed from zero. The theorem result includes both "
                    + "uniqueness statements, the natural source sequence, and the shifted first-column identity. "
                    + "In the formulas, subst(F,U) means F(U), invOfUnit(F,1) is the multiplicative "
                    + "inverse of a constant-one series, and castQ embeds a natural number into the rationals. "
                    + "For b from N to N, B(b) denotes mk(m maps to castQ(b(m))). "
                    + "The construction and existence and uniqueness proofs are repository-derived; "
                    + "the recurrence, source equation and shifted-column assertion are the cited source statements.")),
            new DocumentBlock.DisplayFormula(DefinitionsFormula()),
            Node("array", "The antidiagonal array", "The declaration array is the recursively constructed natural-valued two-index array. "
                + "Its recursion is well founded by the lexicographic measure (n+k,n), with all finite-sum endpoints included.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(ArraySource)),
            Node("IsArray", "The array predicate", "IsArray(T) records the zeroth-row equation and the full successor recurrence for every natural n and k, using the finite range k+1.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(ArraySource)),
            Node("IsSource", "The normalized source predicate", "IsSource(F) requires constant coefficient one and the formal substitution equation F.subst(X times invOfUnit(F,1)) = invOfUnit(1-X,1).", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(SeriesSource)),
            Node("phi", "The substitution operator", "phi(F) is F.subst(X times invOfUnit(F,1)); it is defined without reference to the array.", DescribeRole.Definition),
            Node("sourceCoeff", "Triangular source coefficients", "sourceCoeff is the recursively defined rational coefficient function obtained by forcing each coefficient of phi to equal the corresponding coefficient of the geometric series.", DescribeRole.Definition),
            Node("sourceSeries", "The independent source series", "sourceSeries is the power series whose coefficient at m is sourceCoeff(m).", DescribeRole.Definition),
            Node("result", "The complete array-source result", "The result proves IsArray(array), uniqueness of every IsArray witness, IsSource(sourceSeries), uniqueness of every normalized source, existence and uniqueness of a natural source sequence, its zero coefficient, coefficient agreement with sourceSeries, and array(n,0)=b(n+1) for every natural n. "
                + "Finite telescoping of the row recurrence identifies the column series after multiplication by X and addition of one. "
                + "The remainder vanishes at each fixed degree, and source uniqueness gives the coefficient identity.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(ArraySource)))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        AssessedProvenance? provenance = null)
    {
        var id = DescribeId.Create("a392095-" + name.ToLowerInvariant());
        var handle = DeclarationHandle.Create(Prefix + name);
        var blocks = Blocks(Paragraph(Text(prose)));
        if (role == DescribeRole.Definition)
        {
            return Describe.Remark(id, handle, H(title), provenance ?? AssessedProvenance.FromRepo(), blocks);
        }

        return Describe.Lean(id, handle, H(title), StatementSource.FromAuthor(ResultFormula()),
            provenance ?? AssessedProvenance.FromRepo(), blocks, role,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a392095-antidiagonal-source-series"), ResolutionKind.Proved));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula NatSequence() => Seq(N(), To, N());
    private static Formula ArrayType() => Seq(N(), To, N(), To, N());
    private static Formula SeriesType() => Call("PowerSeries", Q());
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula B(string name) => Call("B", F.Id(name));

    private static Formula DefinitionsFormula()
    {
        var t = F.Id("T");
        var f = F.Id("F");
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        Formula Entry(Formula r, Formula c) => new Formula.Apply(t, [r, c]);
        var sum = Seq(new Formula.Subscript(F.Sum, Equal(j, D(0))), Caret, Grp(k),
            Sp, Par(Mul(Entry(n, j), Entry(Sub(k, j), D(0)))));
        return Disp(new Formula.Aligned([
            Seq(Call("IsArray", t), Sp, Iff, Sp, And(
                All("k", N(), Equal(Entry(D(0), k), D(1))),
                All("n", N(), All("k", N(), Equal(Entry(Add(n, D(1)), k),
                    Add(Entry(n, Add(k, D(1))), sum)))))),
            Seq(Call("IsSource", f), Sp, Iff, Sp, And(
                Equal(Call("constantCoeff", f), D(1)),
                Equal(Call("subst", f, Mul(F.Id("X"), Call("invOfUnit", f, D(1)))),
                    Call("invOfUnit", Sub(D(1), F.Id("X")), D(1)))))
        ]));
    }

    private static Formula ResultFormula()
    {
        var a = Named("array");
        var s = Named("sourceSeries");
        var b = F.Id("b");
        var c = F.Id("c");
        var naturalWitness = Seq(Exists, Sp, b, Colon, Sp, NatSequence(), Comma, Sp,
            And(Call("IsSource", B("b")),
                And(All("c", NatSequence(), Imp(Call("IsSource", B("c")), Equal(c, b))),
                    And(Equal(Call("b", D(0)), D(1)),
                        And(All("m", N(), Equal(Call("coeff", F.Id("m"), s),
                                Call("castQ", Call("b", F.Id("m"))))),
                            All("n", N(), Equal(Call("array", F.Id("n"), D(0)),
                                Call("b", Add(F.Id("n"), D(1))))))))));
        return Disp(And(Call("IsArray", a),
            And(All("T", ArrayType(), Imp(Call("IsArray", F.Id("T")), Equal(F.Id("T"), a))),
                And(Call("IsSource", s),
                    And(All("F", SeriesType(), Imp(Call("IsSource", F.Id("F")), Equal(F.Id("F"), s))),
                        naturalWitness)))));
    }
}
