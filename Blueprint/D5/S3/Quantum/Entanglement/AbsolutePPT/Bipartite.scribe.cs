using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class BipartiteDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula C => Seq(Mathbb, Grp(I("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(
        s.Contains('.') ? Seq(I(s.Split('.')[0]), Dot, I(s.Split('.')[1])) : I(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula p) =>
        Seq(Forall, Sp, Parenthesized(Seq(I(s), Colon, t)), Comma, Sp, p);
    private static Formula Eq(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Mul(Formula a, Formula b) => Parenthesized(Seq(a, Cdot, Sp, b));
    private static Formula J => Parenthesized(Seq(I("A"), Times, Sp, I("B")));
    private static Formula Mat => Call("Matrix", J, J, C);
    private static Formula Systems(Formula p) => All("A", I("Type"), All("B", I("Type"), p));
    private static Formula Instance(string s, string t) =>
        Seq(OpenBracket, Call(s, I(t)), CloseBracket, Sp);
    private static Formula TransposeDefinition() => Systems(All("M", Mat,
        All("p", J, All("q", J, Eq(Call("partialTranspose", I("M"), I("p"), I("q")),
            Call("M", Call("Prod.mk", Call("Prod.fst", I("p")), Call("Prod.snd", I("q"))),
                Call("Prod.mk", Call("Prod.fst", I("q")), Call("Prod.snd", I("p")))))))));
    private static Formula ApptDefinition()
    {
        var u = Call("val", I("U"));
        var conjugate = Mul(Mul(u, I("M")), Call("Matrix.conjTranspose", u));
        return Systems(Seq(Instance("Fintype", "A"), Instance("Fintype", "B"),
            Instance("DecidableEq", "A"), Instance("DecidableEq", "B"),
            All("M", Mat, Seq(Call("APPT", I("M")), Iff, Sp,
                All("U", Call("unitaryGroup", J, C),
                    Call("Matrix.PosSemidef", Call("partialTranspose", conjugate)))))));
    }
    private static DocumentBlock Desc(string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("appt-bipartite-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared partial transpose, universal APPT, and finite cyclic Fourier sectors.",
        H("Generic matrix and cyclic-sector primitives"), Blocks(
            Paragraph(Text("Second-factor partial transpose acts on matrices indexed by a product of local types. APPT requires positivity after every global unitary conjugation. These definitions enter the dimension-general contraction decomposition and the five-row attaining family.")),
            Desc("partialTranspose", "Second-factor partial transpose", TransposeDefinition(),
                "For arbitrary local index types A and B, the output entry at ((a,b),(c,d)) is the input entry at ((a,d),(c,b)). No finiteness, decidable equality, equal-cardinality, Hermitian or positivity assumption is imposed. The operation is definitionally equal to KickedIsingNegativityRefutation.partialTranspose over the same Type-star telescope."),
            Desc("APPT", "All-unitary partial-transpose positivity", ApptDefinition(),
                "For every pair of finite local types with Fintype and DecidableEq instances, APPT M says that the second-factor partial transpose of U M U-adjoint is positive semidefinite for every global unitary on A times B. Empty and unequal local dimensions remain admitted. The Type-star telescope and full unitary group are exactly those of QutritPerturbationAttainment.APPT, which is definitionally equal to this predicate. ContractionAttainment.contraction_appt and five_row_attainment use this predicate."),
            Desc("sectorPoint", "The points of a cyclic sector", SectorPointFormula(),
                "For natural n and d, a residue t and a string r of residues indexed by Fin n, sectorPoint t r is the string with kth entry t+r(k). Neither dimension is required to be nonzero."),
            Desc("sectorCoordinate", "The sector label of a string", SectorCoordinateFormula(),
                "For nonzero n, subtract the zeroth coordinate from every coordinate. The resulting label has zeroth coordinate zero; d may be zero."),
            Desc("fourierVector", "A normalized Fourier vector on a sector", FourierVectorFormula(),
                "For nonzero n and d, frequency a and label r, the coefficient at i is the inverse complex coercion of sqrt d times the standard additive character of a times i(0), when i equals sectorPoint i(0) r, and zero otherwise. Normalization and orthogonality are asserted for labels with zeroth coordinate zero by sector_basis."),
            Desc("sector_coordinates", "Recovering a string from its sector coordinates", SectorCoordinatesFormula(),
                "For nonzero n and arbitrary d, the sector label of i vanishes at zero, and translating it by i(0) recovers i. This decomposes every string into its first coordinate and its normalized sector label.", DescribeRole.Theorem),
            Desc("sectorPoint_injective", "Uniqueness of normalized sector coordinates", SectorInjectiveFormula(),
                "For nonzero n, normalized labels r and s and residues t and u, equality of sectorPoint t r and sectorPoint u s forces both t=u and r=s. Evaluation at zero identifies the translating residues, and cancellation identifies all label coordinates. No positivity assumption on d is needed.", DescribeRole.Theorem),
            Desc("fourier_at_point", "A Fourier coefficient at a sector point", FourierAtPointFormula(),
                "For nonzero n and d and a label r vanishing at zero, the Fourier coefficient at sectorPoint t r is exactly the inverse complex coercion of sqrt d times the standard character at a times t.", DescribeRole.Theorem),
            Desc("fourier_off_sector", "Fourier coefficients vanish off their sector", FourierOffSectorFormula(),
                "For nonzero n and d, if i differs from sectorPoint i(0) r, the coefficient of fourierVector a r at i is zero. The label need not be normalized for this implication.", DescribeRole.Theorem),
            Desc("sector_basis", "Orthonormal Fourier vectors across cyclic sectors", SectorBasisFormula(),
                "For n and d at least two, frequencies a and c and labels r and s vanishing at zero, the conjugate dot product of their Fourier vectors is one exactly when both frequencies and both labels agree, and zero otherwise. Distinct normalized sectors have disjoint support. In a fixed sector, summing the character at t times (c-a) gives d at equal frequencies and zero otherwise; the square-root normalization gives unit length. The hypotheses retain the stated bounds on both dimensions.", DescribeRole.Theorem))));

    private static Formula N => Seq(Mathbb, Grp(I("N")));
    private static Formula R => Seq(Mathbb, Grp(I("R")));
    private static Formula Z => Call("ZMod", I("d"));
    private static Formula K => Call("Fin", I("n"));
    private static Formula Strings => new Formula.TypeArrow(Parenthesized(K), Parenthesized(Z));
    private static Formula At(string f, params Formula[] xs) => Call(f, xs);
    private static Formula Zero => D(0);
    private static Formula Neq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conjunction(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implication(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Dims(Formula body) => All("n", N, All("d", N, body));
    private static Formula NonzeroN(Formula body) => Dims(Implication(Neq(I("n"), Zero), body));
    private static Formula NonzeroND(Formula body) => NonzeroN(Implication(Neq(I("d"), Zero), body));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Coefficient(Formula t) => Mul(
        new Formula.Power(Typed(Call("Real.sqrt", Typed(I("d"), R)), C), Seq(Minus, D(1))),
        Call("ZMod.stdAddChar", Mul(I("a"), t)));
    private static Formula Point(Formula t, Formula r) => At("sectorPoint", t, r);
    private static Formula Fourier(string a, string r, Formula i) => At("fourierVector", I(a), I(r), i);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", Parenthesized(condition), Parenthesized(yes), Parenthesized(no));
    private static Formula SectorPointFormula() => Dims(All("t", Z, All("r", Strings,
        All("k", K, Eq(At("sectorPoint", I("t"), I("r"), I("k")),
            Add(I("t"), At("r", I("k"))))))));
    private static Formula SectorCoordinateFormula() => NonzeroN(All("i", Strings,
        All("k", K, Eq(At("sectorCoordinate", I("i"), I("k")),
            Sub(At("i", I("k")), At("i", Zero))))));
    private static Formula FourierVectorFormula() => NonzeroND(All("a", Z, All("r", Strings,
        All("i", Strings, Eq(Fourier("a", "r", I("i")),
            If(Eq(I("i"), Point(At("i", Zero), I("r"))), Coefficient(At("i", Zero)),
                Typed(Zero, C)))))));
    private static Formula SectorCoordinatesFormula() => NonzeroN(All("i", Strings,
        Conjunction(Eq(At("sectorCoordinate", I("i"), Zero), Zero),
            Eq(Point(At("i", Zero), At("sectorCoordinate", I("i"))), I("i")))));
    private static Formula SectorInjectiveFormula() => NonzeroN(All("r", Strings, All("s", Strings,
        Implication(Eq(At("r", Zero), Zero), Implication(Eq(At("s", Zero), Zero),
            All("t", Z, All("u", Z,
                Implication(Eq(Point(I("t"), I("r")), Point(I("u"), I("s"))),
                    Conjunction(Eq(I("t"), I("u")), Eq(I("r"), I("s")))))))))));
    private static Formula FourierAtPointFormula() => NonzeroND(All("a", Z, All("t", Z,
        All("r", Strings, Implication(Eq(At("r", Zero), Zero),
            Eq(Fourier("a", "r", Point(I("t"), I("r"))), Coefficient(I("t"))))))));
    private static Formula FourierOffSectorFormula() => NonzeroND(All("a", Z, All("r", Strings,
        All("i", Strings, Implication(Neq(I("i"), Point(At("i", Zero), I("r"))),
            Eq(Fourier("a", "r", I("i")), Typed(Zero, C)))))));
    private static Formula SectorBasisFormula()
    {
        Formula summand = Mul(Call("star", Fourier("a", "r", I("i"))), Fourier("c", "s", I("i")));
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(I("i"), Strings)), Sp,
            Parenthesized(summand));
        Formula delta = If(Conjunction(Eq(I("a"), I("c")), Eq(I("r"), I("s"))),
            Typed(D(1), C), Typed(Zero, C));
        return NonzeroND(Implication(Leq(D(2), I("n")), Implication(Leq(D(2), I("d")),
            All("a", Z, All("c", Z, All("r", Strings, All("s", Strings,
                Implication(Eq(At("r", Zero), Zero), Implication(Eq(At("s", Zero), Zero),
                    Eq(sum, delta))))))))));
    }
}
