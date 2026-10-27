using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class HarrowParallelChernoffExponentRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/salekhayashiwinter2022adaptive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive number of parallel uses, the product state with qubits zero and one gives an error exponent at least two, excluding convergence to one.",
        H("A product-state bound excludes parallel exponent one"),
        Blocks(
            Paragraph(Text(
                "The input factors are ordered A, C. MatrixMap denotes complex linear maps between matrix spaces, "
                    + "and all matrices below have complex entries. Finite enumerations and decidable equality "
                    + "are supplied by the anonymous bracketed assumptions. ENNReal is the nonnegative extended "
                    + "real line, with truncated subtraction, and EReal is the extended real line with both infinities. "
                    + "Source line numbers refer to cq-channel-PRXQ-revised.14jan22mh+aw.tex in arXiv:2011.06569v3.")),
            Node("harrow-m", "harrowM", "The first channel", HarrowMFormula(),
                AssessedProvenance.FromLiterature(Source),
                "This is the first channel of Example 5, source lines 1406-1417, extended linearly to every "
                    + "matrix x. The output is diagonal. The first three computational basis inputs contribute "
                    + "to the zero output, while the input with both qubits one contributes half its diagonal "
                    + "entry to each output diagonal entry. The formula specifies every entry, including both "
                    + "off-diagonal output entries."),
            Node("harrow-mbar", "harrowMbar", "The second channel", HarrowMbarFormula(),
                AssessedProvenance.FromLiterature(Source),
                "This is the second channel of Example 5, source lines 1413-1419. When C is zero, the "
                    + "Hadamard plus state gives the same contribution to all four output entries. When C is "
                    + "one, the Hadamard plus outcome on A contributes to the one output and the minus "
                    + "outcome contributes to the maximally mixed output. The off-diagonal entries of x "
                    + "in the C-equals-one block therefore occur with the displayed signs."),
            Node("tensor-pow", "tensorPow", "Tensor powers on matrix units", TensorPowFormula(),
                AssessedProvenance.FromRepo(Source),
                "The n-fold tensor power is specified on matrix units and extended linearly. For every pair "
                    + "a, b of input strings, its matrix-unit image has entry equal to the product of the n "
                    + "single-copy entries. Summing these images with coefficients x(a,b) defines the map on "
                    + "arbitrary matrices. The empty product also defines the zeroth tensor power. This is a "
                    + "finite-coordinate realization of the tensor powers appearing at source lines 1300-1306."),
            Node("diamond-norm", "diamondNorm", "Stabilized trace-norm supremum", DiamondNormFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The reference system has the same index type as the input. The supremum ranges over "
                    + "every positive semidefinite matrix rho of trace one on the input and reference. "
                    + "Applying phi to the input and the identity to the reference gives a matrix whose trace "
                    + "norm is included into ENNReal by ENNReal.ofReal. This is the density-matrix "
                    + "optimization for the diamond norm in the discrimination formula at source lines "
                    + "1273-1295. The definition makes sense for every complex linear matrix map; here it "
                    + "is used for differences of tensor powers of the two channels."),
            Node("parallel-error", "parallelError", "Equal-prior parallel error", ParallelErrorFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The equal-prior error probability is half of one minus half the stabilized norm of "
                    + "the channel difference, as at source lines 1303-1306. The expression is evaluated "
                    + "in ENNReal, including its truncated subtraction and extended division, for every "
                    + "natural n."),
            Node("exponent", "exponent", "The base-two error exponent", ExponentFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Real.log and ENNReal.log use natural logarithms. Division by Real.log 2 gives the "
                    + "base-two convention specified at source lines 894-896 and used for the exponent "
                    + "at lines 1308-1315. The natural n is explicitly cast to a real number; the real "
                    + "inverse normalization is then included into EReal by Real.toEReal. For positive n, "
                    + "zero error has exponent positive infinity. The definition also assigns a value "
                    + "at n equal to zero using the extended-real arithmetic conventions."),
            Node("claim", "claim", "The proposed limit one", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "The proposition says that exponent tends to one in EReal as the natural number of "
                    + "parallel uses tends to infinity. It expresses the optimality conjecture at source "
                    + "lines 1510-1514 for the two explicit channels above. It neither assumes positive "
                    + "error at every n nor replaces the infinite exponent of zero error by a finite value."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The limit cannot be one"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First evaluate both channels on the matrix unit at the computational basis pair "
                            + "(0,1). The first output is diagonal with entries 1 and 0, and the second is "
                            + "diagonal with entries 1/4 and 3/4. Next, expanding the tensor-power sums on "
                            + "an arbitrary matrix unit leaves precisely the product of its single-copy "
                            + "entries. If each single-copy output is diagonal, the product output is "
                            + "diagonal too: two unequal output strings differ at some coordinate, where "
                            + "the corresponding off-diagonal factor vanishes.")),
                    Paragraph(Text(
                        "Apply these identities to the constant string of pairs (0,1). For an output "
                            + "string c, let its real weight be the product over coordinates k of 1/4 "
                            + "when c(k) is zero and 3/4 otherwise. The tensor-power channel difference "
                            + "on this matrix unit is diagonal, with entry one minus that weight at the "
                            + "all-zero output string and minus that weight at every other output string. "
                            + "These real entries are included into the complex scalars.")),
                    Paragraph(Text(
                        "Adjoin a reference in the computational basis state given by the constant "
                            + "string of pairs (0,0). The matrix unit at the pair of these two strings "
                            + "is positive semidefinite, since it is diagonal with nonnegative entries, "
                            + "and has trace one. Expansion of the tensor product with the identity "
                            + "shows that the amplified output is diagonal: it has the preceding "
                            + "channel-difference entries when the reference string is this fixed "
                            + "string, and zero entries at every other reference string.")),
                    Paragraph(Text(
                        "The weights sum to one, by interchanging the sum over output strings with "
                            + "the product of the coordinate sums 1/4 + 3/4. The all-zero string has "
                            + "weight (1/4)^n, and every weight lies between zero and one. Consequently "
                            + "the absolute value of the difference entry at c is its weight plus "
                            + "1 minus twice its weight if c is all zero, with no additional term "
                            + "otherwise. The trace norm of a real diagonal matrix is the sum of the "
                            + "absolute values of its entries. Summing first over the reference strings "
                            + "and then over c therefore gives exactly 2 times (1 minus (1/4)^n).")),
                    Paragraph(Text(
                        "The chosen density matrix is one of the matrices in the supremum defining "
                            + "diamondNorm. Hence that norm is at least ENNReal.ofReal of 2 times "
                            + "(1 minus (1/4)^n). Passing this nonnegative expression into ENNReal "
                            + "gives the same expression there. Divide the bound by two and use "
                            + "the order reversal of subtraction from one. Since (1/4)^n is at most "
                            + "one, the two truncated subtractions cancel, yielding parallelError(n) "
                            + "at most (1/4)^n divided by two.")),
                    Paragraph(Text(
                        "For n at least one, weaken this upper bound to (1/4)^n. Both n cast to "
                            + "the reals and Real.log 2 are positive. The ENNReal logarithm is "
                            + "monotone, and the logarithm of (1/4)^n is the real quantity "
                            + "minus 2 times n times Real.log 2, included into EReal. This follows "
                            + "from the real logarithm laws and Real.log 4 equal to twice Real.log 2. "
                            + "Negating the logarithmic inequality and multiplying by the nonnegative "
                            + "inverse normalization gives exponent(n) at least two, since the "
                            + "normalizing factors cancel.")),
                    Paragraph(Text(
                        "Finally every sufficiently large natural n is at least one, so exponent "
                            + "is eventually at least two. If claim held, this inequality would pass "
                            + "to the limit in EReal and give two at most one, a contradiction. "
                            + "The argument excludes the limit one and supplies the stated lower "
                            + "bound; it does not determine the exact optimal asymptotic exponent."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula HarrowMFormula()
    {
        Formula diagonal = Add(
            If(Equal(X("c"), Bit(0)),
                Add(Add(Entry(0, 0, 0, 0), Entry(1, 0, 1, 0)), Entry(0, 1, 0, 1)), Scalar(0)),
            Divide(Entry(1, 1, 1, 1), Scalar(2)));
        return ChannelBinders(Equal(LocalCall("harrowM", X("x"), X("c"), X("d")),
            If(Equal(X("c"), X("d")), diagonal, Scalar(0))));
    }

    private static Formula HarrowMbarFormula()
    {
        Formula plus = Add(Add(Add(Entry(0, 1, 0, 1), Entry(0, 1, 1, 1)),
            Entry(1, 1, 0, 1)), Entry(1, 1, 1, 1));
        Formula minus = Add(Subtract(Subtract(Entry(0, 1, 0, 1), Entry(0, 1, 1, 1)),
            Entry(1, 1, 0, 1)), Entry(1, 1, 1, 1));
        Formula value = Add(Add(Divide(Add(Entry(0, 0, 0, 0), Entry(1, 0, 1, 0)), Scalar(2)),
            If(Conjunction(Equal(X("c"), Bit(1)), Equal(X("d"), Bit(1))),
                Divide(plus, Scalar(2)), Scalar(0))),
            If(Equal(X("c"), X("d")), Divide(minus, Scalar(4)), Scalar(0)));
        return ChannelBinders(Equal(LocalCall("harrowMbar", X("x"), X("c"), X("d")), value));
    }

    private static Formula TensorPowFormula()
    {
        Formula inputs = Arrow(FinOf(X("n")), Iota);
        Formula outputs = Arrow(FinOf(X("n")), Kappa);
        Formula unit = At(Qualified("Matrix", "single"), At(X("a"), X("k")),
            At(X("b"), X("k")), Scalar(1));
        Formula product = Over(Prod, "k", FinOf(X("n")),
            At(X("φ"), unit, At(X("c"), X("k")), At(X("d"), X("k"))));
        return MapBinders(All("n", Naturals(), All("x", MatrixType(inputs, inputs),
            All("c", outputs, All("d", outputs,
                Equal(LocalCall("tensorPow", X("φ"), X("n"), X("x"), X("c"), X("d")),
                    Over(Sum, "a", inputs, Over(Sum, "b", inputs,
                        Multiply(At(X("x"), X("a"), X("b")), product)))))))));
    }

    private static Formula DiamondNormFormula()
    {
        Formula amplified = At(Qualified("D5", "S3", "Quantum", "Foundation",
            "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap", "kron"), X("φ"),
            Typed(Qualified("LinearMap", "id"), MatrixMapType(Iota, Iota)), X("ρ"));
        Formula norm = At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"),
            amplified);
        Formula conditions = Conjunction(At(Qualified("Matrix", "PosSemidef"), X("ρ")),
            Conjunction(Equal(At(Qualified("Matrix", "trace"), X("ρ")), Scalar(1)),
                Equal(X("r"), At(Qualified("ENNReal", "ofReal"), norm))));
        Formula candidates = Seq(OpenBrace, Typed(X("r"), Qualified("ENNReal")), Sp, Mid, Sp,
            Some("ρ", MatrixType(Product(Iota, Iota), Product(Iota, Iota)), conditions), CloseBrace);
        return MapBinders(Equal(Typed(LocalCall("diamondNorm", X("φ")), Qualified("ENNReal")),
            At(Qualified("sSup"), candidates)));
    }

    private static Formula ParallelErrorFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("parallelError", X("n")), Qualified("ENNReal")),
            Divide(Subtract(Typed(D(1), Qualified("ENNReal")),
                Divide(LocalCall("diamondNorm", Subtract(LocalCall("tensorPow", Local("harrowM"), X("n")),
                    LocalCall("tensorPow", Local("harrowMbar"), X("n")))),
                    Typed(D(2), Qualified("ENNReal")))), Typed(D(2), Qualified("ENNReal")))));

    private static Formula ExponentFormula()
    {
        Formula realN = Typed(At(Qualified("Nat", "cast"), X("n")), Reals());
        Formula normalization = At(Qualified("Inv", "inv"),
            Multiply(realN, At(Qualified("Real", "log"), Typed(D(2), Reals()))));
        return All("n", Naturals(), Equal(Typed(LocalCall("exponent", X("n")), Qualified("EReal")),
            Multiply(At(Qualified("Real", "toEReal"), Typed(normalization, Reals())),
                new Formula.Negate(At(Qualified("ENNReal", "log"), LocalCall("parallelError", X("n")))))));
    }

    private static Formula ClaimFormula() => new Formula.Logic(Parenthesized(Local("claim")),
        FormulaLogicOperator.Iff, Parenthesized(At(Qualified("Filter", "Tendsto"), Local("exponent"),
            Qualified("Filter", "atTop"), At(Qualified("nhds"), Typed(D(1), Qualified("EReal"))))));

    private static Formula ChannelBinders(Formula body) => All("x", MatrixType(
        Product(FinOf(D(2)), FinOf(D(2))), Product(FinOf(D(2)), FinOf(D(2)))),
        All("c", FinOf(D(2)), All("d", FinOf(D(2)), body)));
    private static Formula MapBinders(Formula body) => All("ι", Qualified("Type"),
        All("κ", Qualified("Type"), Instance(At(Qualified("Fintype"), Iota),
            Instance(At(Qualified("DecidableEq"), Iota), Instance(At(Qualified("Fintype"), Kappa),
                All("φ", MatrixMapType(Iota, Kappa), body))))));
    private static Formula MatrixMapType(Formula input, Formula output) => At(Qualified("D5", "S3", "Quantum",
        "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"), input, output, Complexes());
    private static Formula MatrixType(Formula rows, Formula columns) =>
        At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula Entry(byte a, byte b, byte c, byte d) =>
        At(X("x"), Pair(Bit(a), Bit(b)), Pair(Bit(c), Bit(d)));
    private static Formula Bit(byte value) => Typed(D(value), FinOf(D(2)));
    private static Formula Scalar(byte value) => Typed(D(value), Complexes());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name switch
    {
        "ι" => Iota,
        "κ" => Kappa,
        "φ" => Varphi,
        "ρ" => Rho,
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Conjunction(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula Over(Formula operation, string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(operation, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
}
