using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class AxialInnerLieForwardRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/gorshkovshpectorov2026axialquestions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simple rational spin factor with four vector coordinates has a selected-axis inner Lie algebra with a proper nonzero ideal.",
        H("Simplicity of the axial algebra does not imply simplicity of the inner Lie algebra"),
        Blocks(
            Describe.Lean(DescribeId.Create("axial-inner-lie-forward-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The rational primitive Jordan-half forward implication"),
                StatementSource.FromAuthor(Disp(
                    new Formula.Logic(Name("claim"), FormulaLogicOperator.Iff, Parens(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The type binder for A has the Lean typeclass assumptions AddCommGroup A, Module ℚ A and FiniteDimensional ℚ A. "
                    + "The bilinear map L defines multiplication by L(a)(b). Its symmetry gives commutativity. "
                    + "IsAxis uses the actual eigenspaces of L(a) at 1, 0 and 1/2. It requires a nonzero idempotent, "
                    + "its line as the 1-eigenspace, spanning by the three eigenspaces and the six products of the Jordan-half fusion table. "
                    + "Distinct eigenspaces are independent. Generates requires every multiplication-closed linear subspace containing X to be the whole space. "
                    + "The selectedLie subalgebra is the Lie span of [L(a), L(b)] for a and b in X. "
                    + "AlgebraSimple means that every subspace stable under all left multiplications is zero or the whole space. "
                    + "In the published forward implication, choose the field ℚ and the Jordan-half fusion law, then restrict to finite dimension "
                    + "and primitive axes. Every such instance of the printed implication yields the displayed claim."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("axial-inner-lie-forward-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The rational spin factor gives a counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Name("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The carrier is ℚ × ℚ⁴, with multiplication (a,u)(b,v) = (ab + u·v, av + bu). "
                    + "The chosen axes are (1/2, ±eᵢ/2) for the four standard basis vectors. "
                    + "Their actual 1-eigenspaces are their own lines, their 0-eigenspaces are the opposite spin lines, "
                    + "and their half-eigenspaces are the vectors perpendicular to the corresponding basis vectors. "
                    + "The two signed axes for each coordinate linearly generate the unit and all basis vectors. "
                    + "If an algebra ideal contains an element with a nonzero vector component, a commutator of two "
                    + "coordinate left multiplications gives a nonzero pure vector in the ideal. Its square is a nonzero "
                    + "rational multiple of the unit. An ideal containing a nonzero scalar also contains the unit, so the algebra is simple. "
                    + "The selected-axis Lie span is isomorphic to the standard so₄(ℚ) acting on the vector coordinates. "
                    + "The frozen isomorphism with so₃(ℚ) × so₃(ℚ) makes the kernel of the second projection a nonzero proper Lie ideal."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var x = F.Id("X");
        var l = F.Id("L");
        var q = Seq(Mathbb, Grp(F.Id("Q")));
        var u = F.Id("a");
        var v = F.Id("b");
        var symmetric = All("a", a, All("b", a, new Formula.Relation(
            Apply(Apply(l, u), v), FormulaRelationOperator.Equal, Apply(Apply(l, v), u))));
        var axes = All("a", a, Imp(
            new Formula.Relation(u, FormulaRelationOperator.MemberOf, x),
            Call("IsAxis", l, u)));
        var innerSimple = Call("IsSimple", q, Parens(Call("selectedLie", l, x)));
        return All("A", Name("Type"),
            All("L", new Formula.TypeArrow(a, Call("End", q, a)),
                All("X", Call("Set", a),
                    Imp(symmetric, Imp(axes, Imp(Call("Generates", l, x),
                        Imp(Call("AlgebraSimple", l), innerSimple)))))));
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string f, params Formula[] args) => Apply(Name(f), args);
    private static Formula Parens(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Parens(body));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.Implies, Parens(right));
}
