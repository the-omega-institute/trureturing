using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.SymmetricPolynomial;

internal sealed class FullSymmetryNonlocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit entire quartic has every zeta symmetry while all four zeros remain off line.",
        H("Full Symmetry Does Not Force Localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-symmetry-nonlocalization"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization."
                        + "full_symmetry_not_fixed_line_localization"),
                H("A fully symmetric entire function with four off-line zeros"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonzero real delta and gamma, the witness is exactly the source "
                            + "quartic P_delta,gamma(s), formed from z = s - 1/2. It is complex "
                            + "differentiable everywhere and satisfies both generators of the "
                            + "source Klein-four symmetry: reflection s maps to 1-s, and complex "
                            + "conjugation commutes with evaluation.")),
                    Paragraph(Text(
                        "The zero condition is an equivalence, not a one-way inclusion: a point "
                            + "is a zero exactly when it belongs to sourceZeros(delta,gamma). "
                            + "That named finite set consists of 1/2 plus or minus delta plus or "
                            + "minus i gamma, has cardinality four, and every zero has real part "
                            + "different from the repository critical abscissa.")),
                    Paragraph(Text(
                        "The second top-level conjunct is the boxed consequence. It negates the "
                            + "universal implication from entire full-zeta symmetry to fixed-line "
                            + "localization, using the same explicit quartic as counterexample. "
                            + "No Riemann-hypothesis assumption or unformalized zero data enters "
                            + "the declaration."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ReflectionLedger")),
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
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
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
            Call("card", zeros), Sp, Eq, Sp, D(4), Sp, Land,
            RowBreak, Grp(),
            allOffLine);
        Formula universalLocalization = Grp(
            Forall, Sp, function, Colon, Sp, functionType, Comma,
            RowBreak, Grp(),
            Call("Differentiable", complexes, function), Sp, Rightarrow, Sp,
            fullSymmetry, Sp, Rightarrow, Sp,
            fixedLine);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, delta, Comma, Sp, gamma, InMacro, Sp, reals, Comma, Sp,
                delta, Sp, Neq, Sp, D(0), Sp, Land, Sp,
                gamma, Sp, Neq, Sp, D(0), Sp, Rightarrow),
            Seq(
                witness, Sp, Land, Sp,
                Neg, universalLocalization, Dot),
        ]));
    }
}
