using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenCriticalRadiusDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden exponential radial coordinates send the critical line to the unit radius and completed reflection to reciprocal radius.",
        H("Golden Critical Radius"),
        Blocks(
            Theorem("golden-critical-radius-pos", "golden_critical_radius_pos",
                "The Golden Critical Radius Is Positive", GoldenCriticalRadiusPosFormula(),
                "The golden critical radius is a real exponential of the scaled normal offset and is therefore strictly positive at every complex point.",
                "Positivity concerns only the coordinate itself and supplies no information about the location of zeros."),
            Theorem("critical-offset-reflection", "critical_offset_reflection",
                "Critical Reflection Negates the Normal Offset", CriticalOffsetReflectionFormula(),
                "Reflection across the critical line reverses the signed real displacement from one half.",
                "The equality is an exact coordinate calculation and does not depend on a function or a zero set."),
            Theorem("golden-critical-radius-eq-one-iff", "golden_critical_radius_eq_one_iff",
                "Unit Golden Radius Characterizes the Critical Line", GoldenCriticalRadiusEqOneIffFormula(),
                "A complex point has golden critical radius one exactly when its real part equals one half.",
                "This equivalence characterizes the coordinate locus only; it does not prove that any specified spectrum lies there."),
            Theorem("golden-critical-radius-reflection", "golden_critical_radius_reflection",
                "Critical Reflection Takes Radius to Its Reciprocal", GoldenCriticalRadiusReflectionFormula(),
                "Negating the normal offset changes the exponential radius into the reciprocal of the original radius.",
                "The result applies pointwise to every complex number, independently of spectral or functional-equation hypotheses."),
            Theorem("reflected-radius-product-one", "reflected_radius_product_one",
                "Every Reflected Pair Has Unit Radius Product", ReflectedRadiusProductOneFormula(),
                "The positive radius of a point multiplied by the reciprocal radius of its reflection is exactly one.",
                "Paired balance does not imply that either individual radius is one."),
            Theorem("all-critical-iff-all-unit-radius", "all_critical_iff_all_unit_radius",
                "A Set Is Critical Exactly When All Its Radii Are Unit", AllCriticalIffAllUnitRadiusFormula(),
                "Every member of a complex set lies on the critical line exactly when every member has golden radius one.",
                "Both universal statements retain set membership as a premise, so nothing is claimed about points outside the chosen set."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenCriticalRadiusPosFormula()
    {
        Formula s = F.Id("s");
        return Statement([Typed(s, Complexes())], Seq(
            D(0), Sp, Lt, Sp, Call("goldenCriticalRadius", s)));
    }

    private static Formula CriticalOffsetReflectionFormula()
    {
        Formula s = F.Id("s");
        return Statement([Typed(s, Complexes())], Seq(
            Call("criticalOffset", Call("criticalReflection", s)), Sp, Eq, Sp,
            Minus, Call("criticalOffset", s)));
    }

    private static Formula GoldenCriticalRadiusEqOneIffFormula()
    {
        Formula s = F.Id("s");
        Formula left = Seq(Call("goldenCriticalRadius", s), Sp, Eq, Sp, D(1));
        Formula right = Seq(RealPart(s), Sp, Eq, Sp, Half());
        return Statement([Typed(s, Complexes())], Equivalence(left, right));
    }

    private static Formula GoldenCriticalRadiusReflectionFormula()
    {
        Formula s = F.Id("s");
        return Statement([Typed(s, Complexes())], Seq(
            Call("goldenCriticalRadius", Call("criticalReflection", s)), Sp, Eq, Sp,
            Inverse(Call("goldenCriticalRadius", s))));
    }

    private static Formula ReflectedRadiusProductOneFormula()
    {
        Formula s = F.Id("s");
        return Statement([Typed(s, Complexes())], Seq(
            Call("goldenCriticalRadius", s), Sp, Times, Sp,
            Call("goldenCriticalRadius", Call("criticalReflection", s)),
            Sp, Eq, Sp, D(1)));
    }

    private static Formula AllCriticalIffAllUnitRadiusFormula()
    {
        Formula z = F.Id("Z"); Formula s = F.Id("s");
        Formula membership = Seq(s, Sp, InMacro, Sp, z);
        Formula critical = Seq(RealPart(s), Sp, Eq, Sp, Half());
        Formula unit = Seq(Call("goldenCriticalRadius", s), Sp, Eq, Sp, D(1));
        Formula allCritical = QuantifiedImplication(s, membership, critical);
        Formula allUnit = QuantifiedImplication(s, membership, unit);
        return Statement([Typed(z, SetOf(Complexes()))], Equivalence(allCritical, allUnit));
    }

    private static Formula QuantifiedImplication(Formula value, Formula premise, Formula conclusion) =>
        Seq(Forall, Sp, Typed(value, Complexes()), Comma, Sp,
            Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula Equivalence(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Leftrightarrow, Sp, Open, right, Close);

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp);
            for (int index = 0; index < binders.Length; index++)
            {
                if (index > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(binders[index]);
            }
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula RealPart(Formula value) => Seq(value, Dot, F.Id("re"));
    private static Formula Half() => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Inverse(Formula value) => Seq(Grp(value), Caret, Grp(Minus, D(1)));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
