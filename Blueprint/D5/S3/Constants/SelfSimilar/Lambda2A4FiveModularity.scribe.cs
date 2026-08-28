using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.SelfSimilar;

internal sealed class Lambda2A4FiveModularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source Gram and Hodge certificates force both five-modular similarities, rank six, "
            + "the two recorded discriminant identities, and their structural forcing certificate.",
        H("Five-Modularity of the Lambda-Squared A4 Lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lambda-squared-a4-is-five-modular"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity."
                        + "lambda2A4_five_modularity"),
                H("The certified Lambda-squared A4 realization is five-modular"),
                StatementSource.FromAuthor(FiveModularityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let L be any integral lattice realization carrying the six-element basis, "
                            + "the displayed Lambda-squared A4 Gram matrix, the integral Hodge "
                            + "operator, and the exact identification of its bilinear dual with "
                            + "the image of J divided by five.")),
                    Paragraph(Text(
                        "The Hodge similitude equation makes that dual identification scale the "
                            + "bilinear form by one fifth. It therefore gives similarity ratio "
                            + "one over square root five; the inverse equivalence gives ratio square "
                            + "root five in the other direction.")),
                    Paragraph(Text(
                        "The six-element integral basis supplies rank six. The determinant of its "
                            + "fixed Gram matrix is 125, yielding separately the source identities "
                            + "five cubed and five raised to six divided by two.")),
                    Paragraph(Text(
                        "The structural certificate transports that same basis through e onto the "
                            + "actual dualSubmodule. Its Gram matrix is one fifth of the source "
                            + "Gram matrix, so Matrix.det_smul gives the sixth-power determinant "
                            + "scale. Dual/source reciprocity and positivity then force the positive "
                            + "value five raised to six divided by two."))),
                DescribeRole.Theorem))));

    private static Formula FiveModularityFormula()
    {
        Formula ambient = F.Id("E");
        Formula form = F.Id("B");
        Formula lattice = F.Id("L");
        Formula basis = F.Id("b");
        Formula hodge = F.Id("J");
        Formula dualEquiv = F.Id("e");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula dual = Call("dualSubmodule", form, lattice);
        Formula smallScale = Seq(Frac, Grp(D(1)), Grp(Sqrt, Grp(D(5))));
        Formula largeScale = Seq(Sqrt, Grp(D(5)));
        Formula discriminant = Call("latticeDiscriminant", form, lattice, basis);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, ambient, Comma, Sp, form, Comma, Sp, lattice, Comma, Sp,
            basis, Comma, Sp, hodge, Comma, Sp, dualEquiv, Comma, RowBreak, Grp(),
            Call("IntegralRealBilinearLattice", ambient, form, lattice), Sp, Land, Sp,
            Call("BasisFin6Z", basis, lattice), Sp, Land, RowBreak, Grp(),
            Call("latticeGram", form, lattice, basis), Sp, Eq, Sp,
            F.Id("lambda2A4Gram"), Sp, Land, RowBreak, Grp(),
            Call("LinearEquiv", dualEquiv, lattice, dual), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Sp, InMacro, Sp, lattice, Comma, Sp,
            Apply(dualEquiv, x), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(5)), Sp, Cdot, Sp, Apply(hodge, x), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, ambient, Comma, Sp,
            Apply(form, Apply(hodge, x), Apply(hodge, y)), Sp, Eq, Sp,
            D(5), Sp, Cdot, Sp, Apply(form, x, y), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("LatticeSimilarity", form, smallScale, lattice, dual),
            Sp, Land, RowBreak, Grp(),
            Call("finrankZ", lattice), Sp, Eq, Sp, D(6),
            Sp, Land, RowBreak, Grp(),
            Call("LatticeSimilarity", form, largeScale, dual, lattice),
            Sp, Land, RowBreak, Grp(),
            discriminant, Sp, Eq, Sp, D(5), Caret, Grp(D(3)),
            Sp, Land, RowBreak, Grp(),
            discriminant, Sp, Eq, Sp, D(5), Caret,
            Grp(Frac, Grp(D(6)), Grp(D(2))),
            Sp, Land, RowBreak, Grp(),
            Call("FiveModularDiscriminantCertificate", form, lattice, basis, dualEquiv), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
