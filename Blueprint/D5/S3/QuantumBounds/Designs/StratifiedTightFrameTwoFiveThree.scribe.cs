using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class StratifiedTightFrameTwoFiveThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/brinkley2026incoherent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit real SUNTF with parameters (D,N,R) = (2,5,3).",
        H("A real SUNTF_R(2, 5, 3) exists"),
        Blocks(
            Paragraph(Text("Example 4.4, last paragraph (arXiv:2610.05302v1): \"We do not yet know whether a SUNTF_R(2, 5, 3) exists, and we leave this for future research.\" Definition 3.2 (real case) defines a stratified family by constant averaged squared inner products between distinct columns, and a SUNTF when every layer is a unit norm tight frame of common dimension.")),
            Node("IsUNTF", "Unit norm tight frames", IsUNTFFormula(),
                "Definition 3.2 requires every vector in a layer to have norm one and requires a positive frame bound A for the sum of squared analysis coefficients. The formal predicate uses EuclideanSpace R (Fin D) and Fin N for the layer.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsStratified", "Stratified families", IsStratifiedFormula(),
                "Definition 3.2 (arXiv:2610.05302v1, Section 3, p. 8) states: \"Let N and R be finite sets of cardinality N > 0 and R > 0, respectively. For each r ∈ R, let (φ_{r,n})_{n∈N} be a finite sequence of unit vectors in a Euclidean space E_r over F. We say (φ_{r,n})_{n∈N, r∈R} is stratified if there exists Λ ≥ 0 such that (1/R) Σ_{r∈R} |⟨φ_{r,n1}, φ_{r,n2}⟩|² = Λ for any distinct n1, n2 ∈ N. If this holds and each layer (φ_{r,n})_{n∈N} is a UNTF for E_r where there exists D > 0 such that dim(E_r) = D for any r ∈ R, we call (φ_{r,n})_{n∈N, r∈R} a SUNTF for (E_r)_{r∈R} or a SUNTF_F(D, N, R).\" Over the real field the absolute values may be represented by squares.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSUNTF", "SUNTF families", IsSUNTFFormula(),
                "A SUNTF_R(D,N,R) is a stratified family whose R layers are unit norm tight frames for real D-dimensional Euclidean spaces.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The nonexistence question", ClaimFormula(),
                "The paper asks whether a SUNTF_R(2, 5, 3) exists. The encoded claim is the negation of that existence statement, so refuting claim proves the requested existence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The construction exists", Disp(new Formula.Not(F.Id("claim"))),
                "Take u = √(3/8) and v = √(5/8). The three layers use the columns (1,0), (u,v), (u,−v), (u,−v), (u,v); (1,0), (u,v), (u,−v), (u,v), (u,−v); and (1,0), (u,v), (u,v), (u,−v), (u,−v). Each layer has unit norms and frame bound 5/2. Across the three layers, the sign words of the four non-anchor columns, namely (+,+,+), (−,−,+), (−,+,−), (+,−,−) (each of length three), agree pairwise in exactly one position, so every averaged squared inner product is 3/8. These exact finite computations refute the encoded nonexistence claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brinkley-fickus-jasper-mixon-2026-suntf-two-five-three"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("stratified-tight-frame-two-five-three-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Sp, Grp(F.Id(name))), [.. args]);
    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula Space(Formula d) => Call("EuclideanSpace", Reals(), Call("Fin", d));
    private static Formula Layer(Formula d, Formula n) => Seq(Call("Fin", n), Sp, To, Sp, Space(d));
    private static Formula StratifiedFamily(Formula d, Formula n, Formula r) =>
        Seq(Call("Fin", r), Sp, To, Sp, Layer(d, n));
    private static Formula Family(Formula d, Formula n) => StratifiedFamily(d, n, D(3));
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula IsUNTFFormula()
    {
        Formula norms = All("n", Call("Fin", F.Id("N")),
            EqTo(Call("norm", Call("phi", F.Id("n"))), D(1)));
        Formula sum = Seq(Sum, Sp, F.Id("n"), Sp,
            Square(Inner(Call("phi", F.Id("n")), F.Id("x"))));
        Formula tight = All("x", Space(F.Id("D")),
            EqTo(sum, Mul(F.Id("A"), Square(Call("norm", F.Id("x"))))));
        Formula body = And(norms, Exists("A", Reals(), And(LtTo(D(0), F.Id("A")), tight)));
        return Disp(All("D", Nats(), All("N", Nats(),
            All("phi", Layer(F.Id("D"), F.Id("N")), IffTo(Call("IsUNTF", F.Id("phi")), body)))));
    }
    private static Formula IsStratifiedFormula()
    {
        Formula inner = Square(Inner(Call("phi", F.Id("r"), F.Id("n1")), Call("phi", F.Id("r"), F.Id("n2"))));
        Formula average = Mul(new Formula.Fraction(D(1), Call("NatCast", F.Id("R"))),
            Seq(Sum, Sp, F.Id("r"), Sp, inner));
        Formula pair = Implies(new Formula.Not(EqTo(F.Id("n1"), F.Id("n2"))),
            EqTo(average, F.Id("lambda")));
        Formula quantified = All("n1", Call("Fin", F.Id("N")),
            All("n2", Call("Fin", F.Id("N")), pair));
        Formula body = Exists("lambda", Reals(), And(LeTo(D(0), F.Id("lambda")), quantified));
        return Disp(All("D", Nats(), All("N", Nats(), All("R", Nats(),
            All("phi", StratifiedFamily(F.Id("D"), F.Id("N"), F.Id("R")),
                IffTo(Call("IsStratified", F.Id("phi")), body))))));
    }
    private static Formula IsSUNTFFormula()
    {
        Formula layers = All("r", Call("Fin", F.Id("R")), Call("IsUNTF", Call("phi", F.Id("r"))));
        return Disp(All("D", Nats(), All("N", Nats(), All("R", Nats(),
            All("phi", StratifiedFamily(F.Id("D"), F.Id("N"), F.Id("R")),
                IffTo(Call("IsSUNTF", F.Id("phi")), And(layers, Call("IsStratified", F.Id("phi")))))))));
    }
    private static Formula ClaimFormula() => Disp(IffTo(F.Id("claim"),
        new Formula.Not(Exists("phi", Family(D(2), D(5)), Call("IsSUNTF", F.Id("phi"))))));
}
