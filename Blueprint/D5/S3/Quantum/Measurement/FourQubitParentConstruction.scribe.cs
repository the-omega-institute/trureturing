using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FourQubitParentConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/FourQubitParentConstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/bluhm2025inclusion");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FourQubitParentConstruction: exact analytic statements for four-qubit white-noise compatibility.",
        H("FourQubitParentConstruction"),
        Blocks(
            Node("Compatible4", "Compatible4", "Definition 2.13 (p. 12): “Let g ∈ ℕ, d ∈ ℕ, and kₓ ∈ ℕ for all x ∈ [g]. Let (Eᵢ∣ₓ)ᵢ∈[kₓ], x ∈ [g] be a collection of g d-dimensional POVMs. These measurements are compatible if there exists another d-dimensional POVM (Jᵢ₁,…,ᵢg)ᵢ₁∈[k₁],…,ᵢg∈[kg] such that” the marginal equality holds. Here g = 4, d = 2 and each outcome set is Bool. The sixteen functions Fin 4 → Bool index the joint outcomes; true denotes the positive sign.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), All("E", Measurements(), Equal(Call("Compatible4", X("E")), And(All("i", Fin(4), Call("IsPOVM", Apply(X("E"), X("i")))), Ex("J", Parents(), And(Call("IsPOVM", X("J")), All("i", Fin(4), All("b", BoolType(), Equal(Apply(X("E"), X("i"), X("b")), Marginal(X("J"), X("i"), X("b"))))))))))),
            Node("noisy", "noisy", "Definition 2.15 (p. 13): “Let k ∈ ℕ and let (Eᵢ)ᵢ∈[k] be a POVM. Let s ∈ [0, 1] be a noise parameter. Then, we define the POVM (Eᵢ(s))ᵢ∈[k] with” Eᵢ(s) := sEᵢ + (1 − s)I/k “as the noisy version of (Eᵢ)ᵢ∈[k].” Here k = 2 and real scalars act on complex matrices.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), All("s", Reals(), All("E", Measurements(), All("i", Fin(4), All("b", BoolType(), Equal(Call("noisy", X("s"), X("E"), X("i"), X("b")), Add(Smul(X("s"), Apply(X("E"), X("i"), X("b"))), Smul(Subtract(Num(1), X("s")), Smul(Typed(Fraction(Num(1),Num(2)), Complexes()), Identity()))))))))),
            Node("endpoint", "endpoint", "The sharp retained-signal parameter is 2/√13.", DescribeRole.Definition, AssessedProvenance.FromRepo(), Equal(Typed(X("endpoint"), Reals()), Fraction(Num(2), Root(Num(13))))),
            Node("B", "B", "The real coordinates multiply the three Pauli matrices.", DescribeRole.Definition, AssessedProvenance.FromRepo(), All("a", Vectors(), Equal(Call("B", X("a")), Add(Add(Smul(Typed(Apply(X("a"),Num(0)),Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "X"))), Smul(Typed(Apply(X("a"),Num(1)),Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "Y")))), Smul(Typed(Apply(X("a"),Num(2)),Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "Z"))))))),
            Node("B_formula", "B_formula", "The Pauli expansion gives these four complex matrix entries.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("a", Vectors(), Equal(Call("B", X("a")), Mat(Typed(Apply(X("a"),Num(2)),Complexes()), Subtract(Typed(Apply(X("a"),Num(0)),Complexes()), Multiply(Qualified("Complex","I"), Typed(Apply(X("a"),Num(1)),Complexes()))), Add(Typed(Apply(X("a"),Num(0)),Complexes()), Multiply(Qualified("Complex","I"), Typed(Apply(X("a"),Num(1)),Complexes()))), Negate(Typed(Apply(X("a"),Num(2)),Complexes())))))),
            Node("B_real_smul", "B_real_smul", "The Bloch matrix is homogeneous for the real scalar action.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("c", Reals(), All("a", Vectors(), Equal(Call("B", Smul(X("c"),X("a"))), Smul(X("c"), Call("B",X("a"))))))),
            Node("B_neg", "B_neg", "Negating the vector negates its Bloch matrix.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("a", Vectors(), Equal(Call("B", Negate(X("a"))), Negate(Call("B",X("a")))))),
            Node("B_sum", "B_sum", "The Bloch expansion commutes with finite sums.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("U", X("Type"), All("s", Call("Finset", X("U")), All("a", Arrow(X("U"), Vectors()), Equal(Call("B", SumIn("i",X("s"), Apply(X("a"),X("i")))), SumIn("i",X("s"), Call("B",Apply(X("a"),X("i"))))))))),
            Node("norm_sq_coords", "norm_sq_coords", "The squared Euclidean norm is the sum of the three coordinate squares.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("a", Vectors(), Equal(Pow(Norm(X("a")),2), Add(Add(Pow(Apply(X("a"),Num(0)),2), Pow(Apply(X("a"),Num(1)),2)), Pow(Apply(X("a"),Num(2)),2))))),
            Node("trace_B_mul", "trace_B_mul", "The trace pairing of Bloch matrices is twice the real inner product.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("a", Vectors(), All("b", Vectors(), Equal(Apply(Qualified("Matrix","trace"),Multiply(Call("B",X("a")),Call("B",X("b")))), Typed(Multiply(Num(2), Call("inner",Reals(),X("a"),X("b"))), Complexes()))))),
            Node("scalarB", "scalarB", "A scalar identity is added to the traceless Bloch matrix.", DescribeRole.Definition, AssessedProvenance.FromRepo(), All("t",Reals(), All("a",Vectors(), Equal(Call("scalarB",X("t"),X("a")), Add(Smul(Typed(X("t"),Complexes()),Identity()), Call("B",X("a"))))))),
            Node("scalarB_posSemidef_iff", "scalarB_posSemidef_iff", "The determinant and diagonal entries give the necessary bound. At the boundary, the square identity expresses the matrix as a positive multiple of its conjugate-transpose square; adding a nonnegative scalar identity yields sufficiency.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("t",Reals(), All("a",Vectors(), Equivalence(Apply(Qualified("Matrix","PosSemidef"),Call("scalarB",X("t"),X("a"))), LE(Norm(X("a")),X("t")))))),
            Node("half_scalarB_posSemidef_iff", "half_scalarB_posSemidef_iff", "Multiplication by the positive scalar 1/2 preserves the positivity criterion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("t",Reals(), All("a",Vectors(), Equivalence(Apply(Qualified("Matrix","PosSemidef"),Smul(Typed(Fraction(Num(1),Num(2)),Complexes()),Call("scalarB",X("t"),X("a")))), LE(Norm(X("a")),X("t")))))),
            Node("endpoint_mem_Icc", "endpoint_mem_Icc", "The sharp endpoint lies in the permitted retention interval.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), Member(X("endpoint"),Interval(Num(0),Num(1)))),
            Node("compatible_of_parent", "compatible_of_parent", "A POVM with these marginal sums establishes compatibility.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("E",Measurements(),All("J",Parents(),Implication(Call("IsPOVM",X("J")),Implication(All("i",Fin(4),All("b",BoolType(),Equal(Apply(X("E"),X("i"),X("b")),Marginal(X("J"),X("i"),X("b"))))),Call("Compatible4",X("E"))))))),
            Node("all_povms_compatible", "all_povms_compatible", "A compact convex sign decomposition follows from the four-vector inequality and the projection theorem. Antipodal effects give a joint parent for unbiased measurements. Each biased effect is obtained by a stochastic channel from a unit-vector effect and the two deterministic effects; applying these channels to the parent preserves every marginal.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("E",Measurements(),Implication(All("i",Fin(4),Call("IsPOVM",Apply(X("E"),X("i")))),Call("Compatible4",Call("noisy",X("endpoint"),X("E"))))))), []));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role, AssessedProvenance provenance, Formula formula) => Describe.Lean(
        DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula BoolType() => X("Bool");
    private static Formula Vectors() => Call("EuclideanSpace", Reals(), Fin(3));
    private static Formula Matrices() => Call("Matrix", Fin(2), Fin(2), Complexes());
    private static Formula Signs() => Arrow(Fin(4), BoolType());
    private static Formula Measurements() => Arrow(Fin(4), Arrow(BoolType(), Matrices()));
    private static Formula Parents() => Arrow(Signs(), Matrices());
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, long n) => new Formula.Power(a, Num(n));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Root(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implication(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Identity() => Typed(Num(1), Matrices());
    private static Formula Interval(Formula a, Formula b) => Apply(Qualified("Set","Icc"),a,b);
    private static Formula Mat(Formula a, Formula b, Formula c, Formula d) => Seq(Begin, Grp(X("pmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(X("pmatrix")));
    private static Formula SumIn(string v, Formula s, Formula b) => Seq(new Formula.Subscript(Sum, Member(X(v), s)), Sp, b);
    private static Formula Marginal(Formula J, Formula i, Formula b) => Seq(new Formula.Subscript(Sum, Seq(Typed(X("e"),Signs()), Comma, Sp, Equal(Apply(X("e"),i), b))), Sp, Apply(J,X("e")));
}
