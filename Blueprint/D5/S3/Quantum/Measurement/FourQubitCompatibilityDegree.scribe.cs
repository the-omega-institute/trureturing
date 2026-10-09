using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FourQubitCompatibilityDegreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/bluhm2025inclusion");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FourQubitCompatibilityDegree: exact analytic statements for four-qubit white-noise compatibility.",
        H("FourQubitCompatibilityDegree"),
        Blocks(
            Node("feasible", "feasible", "The feasible noise parameters lie in [0, 1] and admit one joint POVM.", DescribeRole.Definition, AssessedProvenance.FromRepo(), All("E", Measurements(), Equal(Call("feasible", X("E")), SetOf("s", Reals(), And(Member(X("s"), Interval(Num(0), Num(1))), Call("Compatible4", Call("noisy", X("s"), X("E")))))))),
            Node("compatDegree", "compatDegree", "Definition 2.16 (p. 13): “Given a g-tuple of measurements E = (E·∣ₓ)ₓ∈[g] on a d-dimensional Hilbert space, having respectively k₁, …, kg outcomes, define their compatibility degree as” sℂ(E) := max{s ∈ [0, 1] : {(Eᵢ∣ₓ(s))ᵢ∈[kₓ]}ₓ∈[g] are compatible}. The closed feasible set has a greatest member, so sSup equals this maximum.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), All("E", Measurements(), Equal(Call("compatDegree", X("E")), Call("sSup", Call("feasible", X("E")))))),
            Node("povmTuples", "povmTuples", "Each of the four measurements is a dichotomic POVM on ℂ².", DescribeRole.Definition, AssessedProvenance.FromRepo(), Equal(Typed(X("povmTuples"), Call("Set", Measurements())), SetOf("E", Measurements(), All("i", Fin(4), Call("IsPOVM", Apply(X("E"), X("i"))))))),
            Node("minCompatDegree", "minCompatDegree", "Definition 2.16 (p. 13): “Consider a measurement setting given by positive integers d, g ∈ ℕ and kₓ ∈ ℕ for all x ∈ [g]. The minimum compatibility degree of this measurement setting is defined as” sℂ(d, g, (k₁, …, kg)) := min{sℂ(E) : E is a g-tuple of measurements on a d-dimensional Hilbert space with k₁, …, kg outcomes}. “If k₁ = … = kg = 2, we write sℂ(d, g) instead.” The extremal tuple attains sInf.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), Equal(Typed(X("minCompatDegree"), Reals()), Call("sInf", Image(X("compatDegree"), X("povmTuples"))))),
            Node("claim", "claim", "Conjecture 6.10 (p. 44): “We conjecture that sℂ(2, 4) = 2/√13. That would mean that the value computed in [BQG+17] is optimal up to numerical precision.” The left side is the minimum of the attained white-noise compatibility degrees over all four-tuples of dichotomic POVMs on ℂ², with the literal marginal and noise definitions.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), Equal(Typed(X("claim"),X("Prop")), Equal(X("minCompatDegree"),Fraction(Num(2),Root(Num(13)))))),
            Node("result", "result", "The sharp four-vector inequality constructs a joint POVM at 2/√13 for every four-tuple of qubit effects, including biased effects. A trine-plus-perpendicular tuple admits an endpoint parent and a matching dual trace bound. Thus its compatibility degree attains the global minimum.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), X("claim"))), []));
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
    private static Formula Matrices() => Call("Matrix", Fin(2), Fin(2), Complexes());
    private static Formula Measurements() => Arrow(Fin(4), Arrow(BoolType(), Matrices()));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Root(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Interval(Formula a, Formula b) => Apply(Qualified("Set","Icc"),a,b);
    private static Formula Image(Formula f, Formula s) => Seq(f, Apos, Apos, Sp, s);
    private static Formula SetOf(string v, Formula t, Formula b) => Seq(OpenBrace, Typed(X(v),t), Sp, Mid, Sp, b, CloseBrace);
}
