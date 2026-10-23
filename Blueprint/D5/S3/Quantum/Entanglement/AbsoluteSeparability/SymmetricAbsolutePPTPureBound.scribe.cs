using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class SymmetricAbsolutePPTPureBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/louvet2025symmetricppt");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite bipartite partial transposes satisfy a universal half-trace lower bound.", H("Half-trace bounds for partial transposition"), Blocks(
            Describe.Lean(DescribeId.Create("lsappt-partialtransposeon"), DeclarationHandle.Create(Prefix + "partialTransposeOn"),
                H("Partial transpose on tensor sites"), StatementSource.FromAuthor(Disp(SitePT())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The entries on a chosen subset of sites are exchanged between the row and column labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-partialtranspose-sum"), DeclarationHandle.Create(Prefix + "partialTranspose_sum"),
                H("Partial transpose of finite sums"), StatementSource.FromAuthor(Disp(TransposeSum())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Partial transposition distributes over finite matrix sums."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-pure-antisymmetric-product-bound"), DeclarationHandle.Create(Prefix + "antisymmetric_product_bound"),
                H("Antisymmetric product estimate"), StatementSource.FromAuthor(Disp(Antisymmetric())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The squared Frobenius mass of the antisymmetric part of a product is at most twice the product of the two squared Frobenius masses. Expanding row wedges and applying Cauchy–Schwarz gives this estimate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-compress-lower"), DeclarationHandle.Create(Prefix + "compress_lower"),
                H("Compression of a lower bound"), StatementSource.FromAuthor(Disp(Compression())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A lower bound by a scalar identity compresses to the same scalar times any Hermitian projector supporting the matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-psd-partialtranspose-half-trace"), DeclarationHandle.Create(Prefix + "psd_partialTranspose_half_trace"),
                H("Half-trace bound"), StatementSource.FromAuthor(Disp(PositiveTraceBound())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The partial transpose of a positive matrix is bounded below by minus half its trace. The spectral decomposition reduces this inequality to unit rank-one matrices."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) => Seq(Operatorname,
        Grp(Seq([.. names.SelectMany((name, index) => index == 0
            ? new Formula[] { X(name) } : new Formula[] { Dot, X(name) })])));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leqf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Plusf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minusf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Timesf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Rat(Formula left, Formula right) => new Formula.Fraction(left, right);


    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula Types => Q("Type");
    private static Formula Matrix(Formula index) => At(Q("Matrix"), index, index, Complexes);
    private static Formula Fn(string variable, Formula type, Formula body) => Seq(Q("fun"), Sp, Typed(X(variable), type), Sp, Mapsto, Sp, body);
    private static Formula Sumf(string variable, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Typed(X(variable), type)), Sp, Parenthesized(body));
    private static Formula Inst(string cls, Formula type) => Seq(OpenBracket, At(Q(cls), type), CloseBracket, Sp);
    private static Formula FiniteTypes(Formula body) => All("I", Types, All("L", Types,
        Seq(Inst("Fintype", X("I")), Inst("DecidableEq", X("I")), Inst("Fintype", X("L")), Inst("DecidableEq", X("L")), body)));
    private static Formula Word => Arr(X("I"), X("L"));


    private static Formula Local(string owner, string name, params Formula[] args) => At(Q("D5", "S3", "Quantum", "Entanglement", "AbsoluteSeparability", owner, name), args);
    private static Formula PT(Formula s, Formula a) => Local("SymmetricAbsolutePPTPureBound", "partialTransposeOn", s, a);
    private static Formula PSD(Formula a) => At(Q("Matrix", "PosSemidef"), a);
    private static Formula Herm(Formula a) => At(Q("Matrix", "IsHermitian"), a);





    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));

    private static Formula PureTypes(Formula body) => All("A", Types, All("B", Types,
        Seq(Inst("Fintype", X("A")), Inst("Fintype", X("B")), body)));
    private static Formula Frobenius(Formula matrix, Formula a, Formula b) => Sumf("i", a, Sumf("j", b,
        At(Q("Complex", "normSq"), At(matrix, X("i"), X("j")))));
    private static Formula Antisymmetric()
    {
        var z = Timesf(At(Q("Matrix", "transpose"), X("V")), X("M"));
        var mass = Sumf("i", X("B"), Sumf("j", X("B"), At(Q("Complex", "normSq"),
            Minusf(At(z, X("i"), X("j")), At(z, X("j"), X("i"))))));
        return PureTypes(All("V", At(Q("Matrix"), X("A"), X("B"), Complexes),
            All("M", At(Q("Matrix"), X("A"), X("B"), Complexes), Leqf(mass,
                Timesf(Timesf(D(2), Parenthesized(Frobenius(X("V"), X("A"), X("B")))), Parenthesized(Frobenius(X("M"), X("A"), X("B"))))))));
    }
    private static Formula SitePT() => All("I", Types, All("L", Types, Seq(Inst("DecidableEq", X("I")),
        All("S", At(Q("Finset"), X("I")), All("rho", Matrix(Word), Eqn(PT(X("S"), X("rho")),
            Fn("x", Word, Fn("y", Word, At(X("rho"), At(Q("Finset", "piecewise"), X("S"), X("y"), X("x")),
                At(Q("Finset", "piecewise"), X("S"), X("x"), X("y")))))))))));
    private static Formula PositiveTraceBound() => FiniteTypes(All("S", At(Q("Finset"), X("I")),
        All("A", Matrix(Word), Imp(PSD(X("A")), PSD(Plusf(PT(X("S"), X("A")),
            Smul(Rat(At(Q("Complex", "re"), At(Q("Matrix", "trace"), X("A"))), D(2)), Typed(D(1), Matrix(Word)))))))));
    private static Formula Compression() => All("I", Types, Seq(Inst("Fintype", X("I")), Inst("DecidableEq", X("I")),
        All("A", Matrix(X("I")), All("Q", Matrix(X("I")), All("a", Reals,
            Imp(Herm(X("Q")), Imp(Eqn(Timesf(X("Q"), X("Q")), X("Q")),
                Imp(Eqn(Timesf(Timesf(X("Q"), X("A")), X("Q")), X("A")),
                    Imp(PSD(Plusf(X("A"), Smul(X("a"), Typed(D(1), Matrix(X("I")))))),
                        PSD(Plusf(X("A"), Smul(X("a"), X("Q")))))))))))));
    private static Formula TransposeSum() => All("I", Types, All("L", Types, Seq(Inst("DecidableEq", X("I")), All("J", Types, All("S", At(Q("Finset"), X("I")),
        All("F", Arr(X("J"), Matrix(Word)), All("s", At(Q("Finset"), X("J")),
            Eqn(PT(X("S"), At(Q("Finset", "sum"), X("s"), X("F"))), At(Q("Finset", "sum"), X("s"),
                Fn("i", X("J"), PT(X("S"), At(X("F"), X("i")))))))))))));

}
