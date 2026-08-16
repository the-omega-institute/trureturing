using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class UnitaryNaturalSelectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No unit choice on finite subspaces is natural under every unitary symmetry.",
        H("No Unitary-Natural Orthogonal Selector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("there-is-no-unitary-natural-orthogonal-selector"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/UnitaryNaturalSelector."
                        + "no_unitary_natural_orthogonal_selector"),
                H("There is no unitary-natural orthogonal selector"),
                StatementSource.FromAuthor(UnitaryNaturalSelectorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be an infinite-dimensional real or complex inner-product space. "
                            + "There is no rule assigning every finite-dimensional subspace M "
                            + "a unit vector in its orthogonal complement while commuting with "
                            + "every surjective linear isometry of H.")),
                    Paragraph(Text(
                        "Apply naturality at the zero subspace to the negative identity isometry. "
                            + "The zero subspace is finite-dimensional and fixed by negation, so "
                            + "the selected vector must equal its own negative. Scalar "
                            + "cancellation makes it zero, contradicting its prescribed norm one. "
                            + "The proof does not use completeness, so the formal result is "
                            + "stronger than the Hilbert-space source statement.")),
                    Paragraph(Text(
                        "This does not contradict the existing FiniteLayerProjectionEscape theorem, "
                            + "which supplies a unit vector separately whenever an orthogonal "
                            + "residual is nonzero. The obstruction is the demand that all choices "
                            + "be natural under every unitary symmetry.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no theorem for the full "
                            + "no-go statement. Loogle supplied LinearIsometryEquiv.neg, the "
                            + "finite-dimensional zero-subspace instance, and preservation of "
                            + "finite dimensionality under Submodule.map. The attempted LeanSearch "
                            + "API request returned HTTP 404 and is not counted as a negative hit."))),
                DescribeRole.Theorem))));

    private static Formula UnitaryNaturalSelectorFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula selector = F.Id("eta");
        Formula subspace = F.Id("M");
        Formula unitary = F.Id("U");
        Formula finiteSubspaces = Call("FiniteSubspace", scalar, space);
        Formula chosen = Call("select", selector, subspace);
        Formula orthogonal = Seq(subspace, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Underscore,
            Grp(scalar), Open, space, Close, CloseBracket, Comma, Esc,
            Neg, Operatorname, Grp(F.Id("FiniteDimensional")), Underscore,
            Grp(scalar), Open, space, Close, Sp, Rightarrow, Sp,
            Neg, Exists, Sp, selector, Colon, Sp, finiteSubspaces, Sp, To, Sp, space,
            Comma, Esc,
            Open, Forall, Sp, subspace, Sp, InMacro, Sp, finiteSubspaces, Comma, Esc,
            chosen, Sp, InMacro, Sp, orthogonal, Sp, Land, Sp,
            Call("norm", chosen), Sp, Eq, Sp, D(1), Close, Sp, Land, Sp,
            Open, Forall, Sp, unitary, Sp, InMacro, Sp, Call("Unitary", space), Comma,
            Sp, subspace, Sp, InMacro, Sp, finiteSubspaces, Comma, Esc,
            Call("select", selector, Call("map", unitary, subspace)), Sp, Eq, Sp,
            Call("map", unitary, chosen), Close, Dot));
    }
}
