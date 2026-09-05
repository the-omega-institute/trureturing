using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.SymmetricPolynomial;

internal sealed class SymmetryNonlocalizationRiemannStabilizerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/SymmetricPolynomial/SymmetryNonlocalizationRiemannStabilizer."
            + "full_symmetry_nonlocalization_and_rh_stabilizer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fully symmetric quartic can have only off-line zeros, while RH says every "
            + "nontrivial zeta zero is mirror-fixed.",
        H("Symmetry Nonlocalization and Riemann Stabilizers"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetry-nonlocalization-and-rh-stabilizer"),
            DeclarationHandle.Create(Declaration),
            H("Full symmetry does not localize zeros"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For arbitrary real delta and gamma, the witness is exactly "
                        + "P_delta,gamma(s) = (((s - 1/2) - delta)^2 + gamma^2) "
                        + "(((s - 1/2) + delta)^2 + gamma^2). It is complex differentiable "
                        + "everywhere and is invariant under s mapping to 1-s, while complex "
                        + "conjugation commutes with evaluation.")),
                Paragraph(Text(
                    "Its zero condition is equivalent to membership in the displayed source "
                        + "set {1/2 + delta + i gamma, 1/2 + delta - i gamma, "
                        + "1/2 - delta + i gamma, 1/2 - delta - i gamma}. The set may collapse "
                        + "when either coordinate is zero. Whenever delta is nonzero, every "
                        + "zero remains off the critical line.")),
                Paragraph(Text(
                    "Under nonzero delta, the same witness refutes the universal implication "
                        + "from entire full-zeta symmetry to fixed-line localization. The final "
                        + "conjunct uses "
                        + "Mathlib's exact nontrivial-zero premises and identifies the source J "
                        + "with mirror(rho) = 1 - conj(rho): RiemannHypothesis holds exactly "
                        + "when every such zero is fixed by mirror."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization")),
        ]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula function = F.Id("F");
        Formula point = F.Id("s");
        Formula rho = Rho;
        Formula n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula functionType = Seq(complexes, Sp, To, Sp, complexes);
        Formula quartic = Call("offCriticalQuartic", delta, gamma);
        Formula zeros = Call("sourceZeros", delta, gamma);
        Formula value = Apply(function, point);
        Formula reflectionValue = Apply(function, Seq(D(1), Sp, Minus, Sp, point));
        Formula conjugateValue = Apply(function, Call("conj", point));
        Formula reflectionSymmetry = Grp(
            Forall, Sp, point, Colon, Sp, complexes, Comma, Sp,
            reflectionValue, Sp, Eq, Sp, value);
        Formula conjugationSymmetry = Grp(
            Forall, Sp, point, Colon, Sp, complexes, Comma, Sp,
            conjugateValue, Sp, Eq, Sp, Call("conj", value));
        Formula fullSymmetry = Seq(
            reflectionSymmetry, Sp, Land, Sp, conjugationSymmetry);
        Formula exactZeros = Grp(
            Forall, Sp, point, Colon, Sp, complexes, Comma, Sp,
            value, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            point, Sp, InMacro, Sp, zeros);
        Formula allOffLine = Grp(
            Forall, Sp, point, Colon, Sp, complexes, Comma, Sp,
            value, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("re", point), Sp, Neq, Sp, F.Id("criticalAbscissa"));
        Formula fixedLine = Grp(
            Forall, Sp, point, Colon, Sp, complexes, Comma, Sp,
            value, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("re", point), Sp, Eq, Sp, F.Id("criticalAbscissa"));

        Formula universalLocalization = Grp(
            Forall, Sp, function, Colon, Sp, functionType, Comma,
            RowBreak, Grp(),
            Call("Differentiable", complexes, function), Sp, Rightarrow, Sp,
            fullSymmetry, Sp, Rightarrow, Sp,
            fixedLine);
        Formula nonlocalization = Grp(
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Grp(allOffLine, Sp, Land, Sp,
                Neg, fixedLine, Sp, Land, Sp,
                Neg, universalLocalization));
        Formula witness = Grp(
            Exists, Sp, function, Colon, Sp, functionType, Comma,
            RowBreak, Grp(),
            function, Sp, Eq, Sp, quartic, Sp, Land,
            RowBreak, Grp(),
            Call("Differentiable", complexes, function), Sp, Land,
            RowBreak, Grp(),
            fullSymmetry, Sp, Land,
            RowBreak, Grp(),
            exactZeros, Sp, Land,
            RowBreak, Grp(),
            nonlocalization);

        Formula trivialZero = Grp(
            Exists, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            rho, Sp, Eq, Sp,
            Minus, D(2), Sp, Cdot, Sp, Grp(n, Sp, Plus, Sp, D(1)));
        Formula mirrorFixed = Seq(
            Forall, Sp, rho, Colon, Sp, complexes, Comma, Sp,
            Call("riemannZeta", rho), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Neg, trivialZero, Sp, Rightarrow, Sp,
            rho, Sp, Neq, Sp, D(1), Sp, Rightarrow, Sp,
            Call("mirror", rho), Sp, Eq, Sp, rho);
        Formula rhCriterion = Grp(
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))), Sp,
            Leftrightarrow, Sp, Grp(mirrorFixed));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, delta, Comma, Sp, gamma, InMacro, Sp, reals, Comma),
            Seq(
                witness, Sp, Land, Sp,
                RowBreak, Grp(), rhCriterion, Dot),
        ]));
    }
}
