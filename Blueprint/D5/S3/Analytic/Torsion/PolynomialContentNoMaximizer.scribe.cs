using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Torsion;

internal sealed class PolynomialContentNoMaximizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Geometry/kraussimanek2024polynomialcontent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial content has no maximizer on suitable unit-area polygons.",
        H("Kraus–Simanek Conjecture 2.1"),
        Blocks(
            Entry("claim", "claim", "claim", Disp(new Formula.Relation(V("claim"), FormulaRelationOperator.Equivalent, Seq(Forall, Sp, V("N"), Colon, Sp, Nat, Comma, Sp, Seq(Exists, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, Seq(Neg, Sp, Parenthesized(Seq(Exists, Sp, V("P"), Colon, Sp, new Formula.Apply(V("Set"), [ComplexType]), Comma, Sp, new Formula.Logic(Parenthesized(new Formula.Apply(new Formula.Apply(V("IsPolygonRegion"), [V("n")]), [V("P")])), FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(V("volume"), [V("P")]), FormulaRelationOperator.Equal, D(1))), FormulaLogicOperator.And, Parenthesized(Seq(Forall, Sp, V("Q"), Colon, Sp, new Formula.Apply(V("Set"), [ComplexType]), Comma, Sp, new Formula.Logic(Parenthesized(new Formula.Apply(new Formula.Apply(V("IsPolygonRegion"), [V("n")]), [V("Q")])), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(V("volume"), [V("Q")]), FormulaRelationOperator.Equal, D(1))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Apply(new Formula.Apply(V("rhoN"), [V("N")]), [V("Q")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(new Formula.Apply(V("rhoN"), [V("N")]), [V("P")])))))))))))))))))), "Conjecture 2.1, p. 3: “For each N ∈ ℕ, there is an n ∈ ℕ so that among all n-gons with area 1, ρ_N has no maximizer.” The natural N includes zero. The existential polygon index n represents n + 3 sides; the area is planar volume. Polygon.boundary is the closed path v₀ → v₁ → ⋯ → vₙ₊₂ → v₀ in IsPolygonRegion.", DescribeRole.Definition, true),
            Entry("result", "result", "result", Disp(Seq(Forall, Sp, V("N"), Colon, Sp, Nat, Comma, Sp, Seq(Exists, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, Seq(Neg, Sp, Parenthesized(Seq(Exists, Sp, V("P"), Colon, Sp, new Formula.Apply(V("Set"), [ComplexType]), Comma, Sp, new Formula.Logic(Parenthesized(new Formula.Apply(new Formula.Apply(V("IsPolygonRegion"), [V("n")]), [V("P")])), FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(V("volume"), [V("P")]), FormulaRelationOperator.Equal, D(1))), FormulaLogicOperator.And, Parenthesized(Seq(Forall, Sp, V("Q"), Colon, Sp, new Formula.Apply(V("Set"), [ComplexType]), Comma, Sp, new Formula.Logic(Parenthesized(new Formula.Apply(new Formula.Apply(V("IsPolygonRegion"), [V("n")]), [V("Q")])), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(V("volume"), [V("Q")]), FormulaRelationOperator.Equal, D(1))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Apply(new Formula.Apply(V("rhoN"), [V("N")]), [V("Q")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(new Formula.Apply(V("rhoN"), [V("N")]), [V("P")]))))))))))))))))), "Put m = max(3, N + 2). Alternate long and short radial vertices at angles π/m, choosing the short radius so that the area is one. The resulting 2m-gon is simple. Rotation through 2π/m annihilates the moments of orders 1 through N + 1, so the polynomial content equals the second moment. A positive-area cap has squared norm bounded below by a positive multiple of the squared long radius. Thus the polynomial content is unbounded, and no polygon can maximize it.", DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("kraus-simanek-2024-polynomial-content-no-maximizer"),
                ResolutionKind.Proved) : null);

    private static Formula V(string value) => F.Id(value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula ComplexType => Seq(Mathbb, Grp(V("C")));
}
