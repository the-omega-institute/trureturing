using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class AxialInnerLieConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/gorshkovshpectorov2026axialquestions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational primitive Jordan-half axial algebra with a proper scalar ideal has simple selected-axis inner Lie algebra.",
        H("Simplicity of the inner Lie algebra does not imply simplicity of the axial algebra"),
        Blocks(
            Describe.Lean(DescribeId.Create("axial-inner-lie-converse-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The rational primitive Jordan-half converse"),
                StatementSource.FromAuthor(Disp(
                    new Formula.Logic(Name("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The endomorphisms in End(ℚ,A) are ℚ-linear. "
                    + "The linear map L defines multiplication by L(a)(b). Its symmetry gives commutativity. "
                    + "IsAxis uses the actual eigenspaces of L(a) at 1, 0 and 1/2. It requires a nonzero idempotent, "
                    + "its line as the 1-eigenspace, spanning by the three eigenspaces and the six products of the Jordan-half fusion table. "
                    + "Distinct eigenspaces are independent. Generates requires every multiplication-closed linear subspace containing X to be the whole space. "
                    + "The selectedLie subalgebra is the Lie span of [L(a), L(b)] for a and b in X. "
                    + "AlgebraSimple means that every subspace stable under all left multiplications is zero or the whole space. "
                    + "In the published converse, choose the field ℚ and the Jordan-half fusion law, then restrict to finite dimension "
                    + "and primitive axes. Every such instance of the printed implication yields the displayed claim."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("axial-inner-lie-converse-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The scalar summand gives a counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Name("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The algebra is (ℚ × ℚ³) × ℚ with the spin product on the first factor and the ordinary scalar product on the last factor. "
                    + "The chosen generators are the two spin axes for each coordinate and the last-factor unit z. "
                    + "The spin axes have 1-eigenline equal to their own line, 0-eigenspace given by the opposite spin line and ℚz, "
                    + "and half-eigenspace given by the perpendicular vectors. For z the corresponding spaces are ℚz, the spin factor and zero. "
                    + "The chosen axes already span linearly and ℚz is a nonzero proper ideal. "
                    + "Every chosen commutator acts by a skew matrix on the three vector coordinates and by zero on both scalar coordinates. "
                    + "The positive-coordinate axes yield the elementary skew matrices up to a factor of 1/4. "
                    + "The frozen orthogonal simplicity theorem applies to the resulting Lie equivalence."))),
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
        var innerSimple = Call("IsSimple", q, Parenthesized(Call("selectedLie", l, x)));
        return All("A", Name("Type"), Seq(
            OpenBracket, Call("AddCommGroup", a), CloseBracket, Sp,
            OpenBracket, Call("Module", q, a), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", q, a), CloseBracket, Sp,
            All("L", Call("LinearMap", q, a, Call("End", q, a)),
                All("X", Call("Set", a),
                    Imp(symmetric, Imp(axes, Imp(Call("Generates", l, x),
                        Imp(innerSimple, Call("AlgebraSimple", l)))))))));
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string f, params Formula[] args) => Apply(Name(f), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
