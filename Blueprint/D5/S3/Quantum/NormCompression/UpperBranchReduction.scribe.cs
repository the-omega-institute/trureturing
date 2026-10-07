using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class UpperBranchReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/NormCompression/UpperBranchReduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2008normcompression");
    private static readonly Formula J = F.Id("J"), HA = F.Id("HA"), HB = F.Id("HB"), C = F.Id("C");
    private static readonly Formula A = F.Id("A"), B = F.Id("B"), P = F.Id("p"), W = F.Id("w");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every real p at least two, a finite family of compatible complex block columns admits nonnegative square-root weights supported on at most three original columns. The compression Gram matrix is unchanged and the Schatten p-norm does not decrease. Therefore the upper norm-compression inequality for one, two and three columns implies it for every finite number of columns.",
        H("Upper norm compression reduces to three block columns"),
        Blocks(
            Node("power", "Singular-value power sum", PowerFormula(),
                "Page 2 defines the Schatten norm by ‖A‖_p = (Tr(|A|^p))^(1/p). The finite trace power is the sum of powers of LinearMap.singularValues of Matrix.toEuclideanLin A. Only nonzero singular values occur in its Finsupp.support; at the exponents used below, omitted zero values contribute zero.", "schattenPow", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("norm", "Schatten norm", NormFormula(),
                "Page 2, verbatim: \"For a general matrix or operator A, they are defined as\" followed by ‖A‖_p = (Tr(|A|^p))^(1/p). Real.rpow is used for both powers, and 1/p is real division. The reduction only uses p >= 2, so neither p = 0 nor the infinite-exponent norm is involved.", "schattenNorm", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("assemble", "Compatible block-column concatenation", AssembleFormula(),
                "Page 2 writes T as the two block rows (A_1,...,A_N) and (B_1,...,B_N). J indexes the columns, HA and HB index the row spaces, and C j is the column space shared by A j and B j. Sigma C concatenates these column spaces, which may have different finite dimensions. Matrix.fromRows stacks the two blocks.", "assemble", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rescale", "Square-root column rescaling", RescaleFormula(),
                "Both blocks of column j are multiplied by the same nonnegative square root. The displayed coercion casts the real scalar to Complex. In the reduction, w j >= 0, including zero weights.", "rescale", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compression", "The two-row norm compression", CompressionFormula(),
                "Page 2, verbatim: \"I denote by 𝒞ₚ(T) its Schatten p-norm compression,\" followed by the two scalar rows (‖A_1‖_p,...,‖A_N‖_p) and (‖B_1‖_p,...,‖B_N‖_p). Row i = 0 is the A row; the other element of Fin 2 is the B row. Each nonnegative real entry is cast to Complex.", "compression", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("compressiongram", "Compression Gram matrix", CompressionGramFormula(),
                "The compression Gram matrix uses Matrix.conjTranspose and lives on the fixed row type Fin 2. Its entries are the sums of the squared top norms, squared bottom norms and products of the two norms.", "compressionGram", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("rescaling", "Three active weights preserve the compression Gram matrix", ReductionFormula(false),
                "The three real moments are (‖A_j‖_p^2, ‖B_j‖_p^2, ‖A_j‖_p ‖B_j‖_p). A signed dependence among more than three active moment vectors gives two nonnegative boundary weights whose convex combination is the original weight. One boundary has no smaller convex Schatten power. Repeating the face move terminates with at most three active weights. Columns with both blocks zero are discarded before the face moves.", "rescaling_upper_three", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("selected", "At most three actual block columns", ReductionFormula(true),
                "Restricting to the finite support of w deletes every zero-weight column. The selected index is a subtype member, and val returns its original column index. The compression Gram matrix is exactly the original one, and the Schatten norm of the selected, rescaled block matrix is at least the original norm. The row dimensions and the individual column dimensions are unrestricted finite types.", "upper_three_columns", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("r1", "The three-column case implies the upper branch", R1Formula(),
                "Conjecture 1, page 2, verbatim: \"Let T be a general matrix partitioned in 2 × N blocks, and let 𝒞ₚ(T) be its norm compression using the Schatten p-norm, then the following norm compression inequalities hold:\" The upper branch is ‖T‖_p <= ‖𝒞ₚ(T)‖_p, p >= 2. The theorem proves the implication from this inequality for one, two and three columns to the inequality for arbitrary finite J, at the same p and row dimensions. The variables Ap and Bp represent Lean A' and B'. The empty selected family is handled separately. It proves a reduction; the unrestricted upper inequality on 2 < p < 4 remains open. The lower branch requires trace-power concavity and is not asserted here.", "r1_upper", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("audenaert-r1-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula TypeU() => F.Id("Type");
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(Formula a, Formula b) => Call("Matrix", a, b, Complex());
    private static Formula SumType(Formula a, Formula b) => Call("Sum", a, b);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula Nonnegative(Formula w, Formula jtype) => All("j", jtype, Le(D(0), App(w, F.Id("j"))));
    private static Formula Support(Formula w) => QCall("Set.Finite", "toFinset", QCall("Set", "toFinite", QCall("Function", "support", w)));
    private static Formula Norm(Formula x) => Call("schattenNorm", P, x);
    private static Formula ColumnType(Formula rows, Formula domain, Formula dims) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, domain)), Comma, Sp, Mat(rows, App(dims, F.Id("j"))));

    private static Formula OverMatrices(Formula body)
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula result = All("p", Real(), All("A", Mat(m, n), body));
        result = Inst(Call("DecidableEq", m), Inst(Call("DecidableEq", n), result));
        result = Inst(Call("Fintype", m), Inst(Call("Fintype", n), result));
        return All("m", TypeU(), All("n", TypeU(), result));
    }

    private static Formula PowerFormula()
    {
        Formula i = F.Id("i"), t = QCall("Matrix", "toEuclideanLin", A);
        Formula values = QCall("LinearMap", "singularValues", t);
        return OverMatrices(Eq(Call("schattenPow", P, A),
            Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, QCall("Finsupp", "support", values))), Sp,
                Pow(App(values, i), P))));
    }

    private static Formula NormFormula() => OverMatrices(Eq(Call("schattenNorm", P, A),
        Pow(Call("schattenPow", P, A), new Formula.Fraction(D(1), P))));

    private static Formula Family(Formula body, int mode)
    {
        Formula rest = body;
        if (mode > 0)
            rest = Inst(All("j", J, Call("Fintype", App(C, F.Id("j")))),
                Inst(All("j", J, Call("DecidableEq", App(C, F.Id("j")))), rest));
        rest = All("C", Arrow(J, TypeU()), rest);
        if (mode > 0)
        {
            rest = Inst(Call("DecidableEq", HA), Inst(Call("DecidableEq", HB), rest));
            if (mode >= 3) rest = Inst(Call("DecidableEq", J), rest);
            rest = Inst(Call("Fintype", HA), Inst(Call("Fintype", HB), rest));
            if (mode >= 2) rest = Inst(Call("Fintype", J), rest);
        }
        return All("J", TypeU(), All("HA", TypeU(), All("HB", TypeU(), rest)));
    }

    private static Formula WithBlocks(Formula body) => All("A", ColumnType(HA, J, C), All("B", ColumnType(HB, J, C), body));

    private static Formula AssembleFormula()
    {
        Formula i = F.Id("i"), jk = F.Id("jk"), fst = QCall("Sigma", "fst", jk), snd = QCall("Sigma", "snd", jk);
        return Family(WithBlocks(All("i", SumType(HA, HB), All("jk", Call("Sigma", C),
            Eq(App(Call("assemble", A, B), i, jk), App(QCall("Matrix", "fromRows", App(A, fst), App(B, fst)), i, snd))))), 0);
    }

    private static Formula RescaleFormula() => All("m", TypeU(), All("n", TypeU(), All("w", Real(),
        All("A", Mat(F.Id("m"), F.Id("n")), Eq(Call("rescale", W, A), Smul(Cast(QCall("Real", "sqrt", W), Complex()), A))))));

    private static Formula CompressionFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula entry = Seq(F.Id("if"), Sp, Parenthesized(Eq(i, D(0))), Sp, F.Id("then"), Sp, Norm(App(A, j)), Sp, F.Id("else"), Sp, Norm(App(B, j)));
        return Family(All("p", Real(), WithBlocks(All("i", Call("Fin", D(2)), All("j", J,
            Eq(App(Call("compression", P, A, B), i, j), Cast(Parenthesized(entry), Complex())))))), 1);
    }

    private static Formula CompressionGramFormula() => Family(All("p", Real(), WithBlocks(
        Eq(Call("compressionGram", P, A, B), Mul(Call("compression", P, A, B), QCall("Matrix", "conjTranspose", Call("compression", P, A, B)))))), 2);

    private static Formula Rescaled(Formula blocks, Formula jtype, bool selected)
    {
        Formula j = F.Id("j"), index = selected ? Call("val", j) : j;
        return LambdaOf("j", jtype, Call("rescale", App(W, index), App(blocks, index)));
    }

    private static Formula ReductionFormula(bool selected)
    {
        Formula domain = selected ? Support(W) : J;
        Formula aa = Rescaled(A, domain, selected), bb = Rescaled(B, domain, selected);
        Formula card = selected ? QCall("Fintype", "card", Support(W)) : QCall("Finset", "card", Support(W));
        Formula bound = Le(Norm(Call("assemble", A, B)), Norm(Call("assemble", aa, bb)));
        Formula gram = Eq(Call("compressionGram", P, aa, bb), Call("compressionGram", P, A, B));
        Formula body = Some("w", Arrow(J, Real()), And(Nonnegative(W, J), And(Le(card, D(3)), And(gram, bound))));
        return Family(All("p", Real(), Imp(Le(D(2), P), WithBlocks(body))), 3);
    }

    private static Formula R1Formula()
    {
        Formula k = F.Id("K"), d = F.Id("D"), a = F.Id("Ap"), b = F.Id("Bp"), j = F.Id("k");
        Formula small = Le(Norm(Call("assemble", a, b)), Norm(Call("compression", P, a, b)));
        small = Imp(Lt(D(0), QCall("Fintype", "card", k)), Imp(Le(QCall("Fintype", "card", k), D(3)), small));
        small = All("Ap", ColumnType(HA, k, d), All("Bp", ColumnType(HB, k, d), small));
        small = Inst(All("k", k, Call("Fintype", App(d, j))), Inst(All("k", k, Call("DecidableEq", App(d, j))), small));
        small = All("D", Arrow(k, TypeU()), small);
        small = All("K", TypeU(), Inst(Call("Fintype", k), Inst(Call("DecidableEq", k), small)));
        Formula target = WithBlocks(Le(Norm(Call("assemble", A, B)), Norm(Call("compression", P, A, B))));
        return Family(All("p", Real(), Imp(Le(D(2), P), Imp(small, target))), 3);
    }
}
