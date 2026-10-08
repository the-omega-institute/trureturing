using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class QubitSupportCoefficientFormsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/li2025genuinely");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula n => F.Id("n");
    private static Formula p => F.Id("p");
    private static Formula c => F.Id("c");
    private static Formula d => F.Id("d");
    private static Formula r => F.Id("r");
    private static Formula j => F.Id("j");
    private static Formula f => F.Id("f");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corresponding coefficient matrices of an ordered complementary two-row support "
        + "are indexed by compositions of the number of columns.",
        H("Counting the forms of a two-row coefficient matrix"),
        Blocks(
            Node("BasisString", "Ordered binary basis strings", BasisFormula(),
                "An n-qubit basis string is a natural number below 2 to the power n. "
                + "Bit positions increase with significance, so the first qubit in the "
                + "source's notation is the most significant digit. Increasing natural-number "
                + "order is the binary order of the occupied basis states.", true),
            Node("Supported", "Support on a qubit set", SupportFormula(),
                "A string supported on P has bit zero at every qubit outside P.", true),
            Describe.Lean(DescribeId.Create("coefficient-forms-config"),
                DeclarationHandle.Create(Prefix + "Config"), H("The complementary row and column factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural numbers n and p, Config n p consists of a nonempty finite "
                    + "set P of bit positions in Fin n, two strings x and y in BasisString n, "
                    + "and a function sigma from Fin p to BasisString n. The string x is "
                    + "supported on P and has bit zero at its greatest position. At every "
                    + "position in P the bit of y is the Boolean complement of the bit of x; "
                    + "outside P its bit is zero. The function sigma is strictly increasing, "
                    + "its strings are supported on the complement of P, and for every position "
                    + "outside P there is a column whose bit is zero and a column whose bit is "
                    + "one. Thus every row qubit changes between the rows and every column "
                    + "qubit changes among the columns. These are the support conditions of "
                    + "Eq. (120), including the absence of a fixed qubit."))), DescribeRole.Definition),
            Node("occupied", "Occupied basis strings", OccupiedFormula(),
                "The first row uses x and the second uses y. Adding a column string inserts "
                + "its bits at disjoint positions, so the addition has no carries.", true),
            Node("form", "The coefficient-index matrix", FormFormula(),
                "The matrix entry is the number of occupied strings preceding that row and "
                + "column. Indices begin at zero in Fin (2 p); adding one gives the subscript "
                + "of b in the source. The columns remain in increasing sigma order and the "
                + "first row has zero at the greatest row position.", true),
            Node("forms", "Forms over all numbers of qubits", FormsFormula(),
                "A form belongs to this set exactly when some configuration on some number "
                + "of qubits has that matrix of coefficient indices.", true),
            Node("formsAt", "Forms on a fixed number of qubits", FormsAtFormula(),
                "Here the number of qubits is fixed, with the same conventions on row and "
                + "column order.", true),
            Node("formOf", "The form associated with a composition", FormOfFormula(),
                "If a column lies in a part starting at s and ending at t, its first-row "
                + "index is j + s and its second-row index is j + t. Reading the rows in "
                + "increasing index order gives a top run and a bottom run of each part's size."),
            Node("formOf_injective", "Recovering the parts", InjectiveFormula(),
                "Subtracting j from each top-row index recovers the start of its part. "
                + "These starts together with the endpoint p recover all composition boundaries.",
                theorem: true),
            Node("necessity", "Every form comes from a composition", NecessityFormula(),
                "Let q be the greatest row position. Group the columns by their bits above q. "
                + "The groups occur consecutively, since the columns are increasing. Within "
                + "a group every first-row string precedes every second-row string: their "
                + "highest differing bit is q. Each row separately preserves column order. "
                + "The nonempty group sizes therefore give the required composition.", theorem: true),
            Node("realization", "Every composition can be realized", RealizationFormula(),
                "Let k be the number of parts and a the largest part. Use ceil(log base 2 a) "
                + "bits below the row bit and ceil(log base 2 k) bits above it. The upper bits "
                + "encode the part index and the lower bits the position within that part. "
                + "Every upper bit varies among the part indices, and every lower bit varies "
                + "inside a largest part. Any extra least significant bits are assigned to "
                + "the row factor, which is zero in the first row and one in the second. "
                + "This preserves the order and leaves no fixed qubit. Both k and a are at "
                + "most p, giving the stated uniform bound.", theorem: true),
            Node("forms_eq_range", "The complete set of forms", RangeFormula(),
                "The prefix decomposition and the construction in the other direction "
                + "identify the forms with the range of the composition map.", theorem: true),
            Node("result", "Answer to the coefficient-matrix question", ResultFormula(),
                "There are exactly 2 to the power p minus one forms, for every positive p, "
                + "and hence for every prime p in Li's question. Compositions of p are counted "
                + "by choices of cuts in its p minus one gaps. Every form is already realized "
                + "at each number of qubits at least twice ceil(log base 2 p) plus one. "
                + "For p equal to two or three this yields the two and four forms recorded "
                + "in the source. The count concerns support indices, independently of the "
                + "nonzero amplitudes in the two factors.", theorem: true,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("li-2025-coefficient-matrix-forms-count"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature = false, bool theorem = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("coefficient-forms-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula FinOf(Formula size) => Call("Fin", size);
    private static Formula Basis(Formula size) => Call("BasisString", size);
    private static Formula ConfigType() => Call("Config", n, p);
    private static Formula MatrixType() => new Formula.TypeArrow(FinOf(D(2)),
        new Formula.TypeArrow(FinOf(p), FinOf(Times(D(2), p))));
    private static Formula Field(Formula obj, string name) => Seq(obj, Dot, Named(name));
    private static Formula Value(Formula obj) => Field(obj, "val");
    private static Formula SizeUpTo(Formula obj, Formula index) => Apply(Field(obj, "sizeUpTo"), index);
    private static Formula Index(Formula obj, Formula col) => Value(Apply(Field(obj, "index"), col));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Times(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula NotMember(Formula a, Formula b) => Seq(Neg, Sp, Parenthesized(Member(a, b)));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Some(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula Hyp(string name, Formula condition, Formula body) =>
        Seq(OpenBracket, F.Id(name), Sp, Colon, Sp, condition, CloseBracket, Sp,
            Rightarrow, Sp, Parenthesized(body));
    private static Formula Bound() => Add(Times(D(2), Call("clog", D(2), p)), D(1));
    private static Formula Positive(Formula body) => Hyp("hp", Le(D(1), p), body);
    private static Formula OverConfig(Formula body) => All("n", N, All("p", N, All("c", ConfigType(), body)));
    private static Formula CompositionMap() => Seq(LambdaLower, Sp, d, Sp, Colon, Sp,
        Call("Composition", p), Comma, Sp, Call("formOf", d));

    private static Formula BasisFormula() => Disp(All("n", N, Eq(Basis(n), FinOf(Pow(D(2), n)))));
    private static Formula SupportFormula()
    {
        Formula P = F.Id("P"), x = F.Id("x"), i = F.Id("i");
        Formula condition = All("i", FinOf(n), Logic(NotMember(i, P), FormulaLogicOperator.Implies,
            Eq(Call("testBit", Value(x), Value(i)), Named("false"))));
        return Disp(All("n", N, All("P", Call("Finset", FinOf(n)), All("x", Basis(n),
            Iff(Call("Supported", P, x), condition)))));
    }
    private static Formula OccupiedFormula()
    {
        Formula row = Seq(Named("if"), Sp, Eq(r, D(0)), Sp, Named("then"), Sp, Value(Field(c, "x")),
            Sp, Named("else"), Sp, Value(Field(c, "y")));
        return Disp(OverConfig(All("r", FinOf(D(2)), All("j", FinOf(p),
            Eq(Call("occupied", c, r, j), Add(Parenthesized(row), Value(Apply(Field(c, "sigma"), j))))))));
    }
    private static Formula FormFormula()
    {
        Formula z = F.Id("z");
        Formula pairs = Seq(FinOf(D(2)), Sp, F.Times, Sp, FinOf(p));
        Formula set = Seq(OpenBrace, z, Sp, Colon, Sp, pairs, Sp, Mid, Sp,
            Lt(Call("occupied", c, Call("fst", z), Call("snd", z)), Call("occupied", c, r, j)),
            CloseBrace);
        return Disp(OverConfig(All("r", FinOf(D(2)), All("j", FinOf(p),
            Eq(Value(Call("form", c, r, j)), Call("card", set))))));
    }
    private static Formula FormsFormula() => Disp(All("p", N, All("f", MatrixType(),
        Iff(Member(f, Call("forms", p)), Some("n", N, Some("c", ConfigType(), Eq(Call("form", c), f)))))));
    private static Formula FormsAtFormula() => Disp(All("n", N, All("p", N, All("f", MatrixType(),
        Iff(Member(f, Call("formsAt", n, p)), Some("c", ConfigType(), Eq(Call("form", c), f)))))));
    private static Formula FormOfFormula() => Disp(All("p", N, All("d", Call("Composition", p),
        All("r", FinOf(D(2)), All("j", FinOf(p), Eq(Value(Call("formOf", d, r, j)),
            Add(Value(j), SizeUpTo(d, Add(Index(d, j), Value(r))))))))));
    private static Formula InjectiveFormula() => Disp(All("p", N,
        Call("Injective", CompositionMap())));
    private static Formula NecessityFormula() => Disp(OverConfig(Some("d", Call("Composition", p),
        Eq(Call("form", c), Call("formOf", d)))));
    private static Formula RealizationFormula() => Disp(All("p", N,
        Positive(All("d", Call("Composition", p), All("n", N, Hyp("hn", Le(Bound(), n),
            Some("c", ConfigType(), Eq(Call("form", c), Call("formOf", d)))))))));
    private static Formula RangeFormula() => Disp(All("p", N, Positive(
        Eq(Call("forms", p), Call("range", CompositionMap())))));
    private static Formula ResultFormula() => Disp(All("p", N, Positive(And(
        Eq(Call("ncard", Call("forms", p)), Pow(D(2), Sub(p, D(1)))),
        All("n", N, Hyp("hn", Le(Bound(), n), Eq(Call("formsAt", n, p), Call("forms", p))))))));
}
