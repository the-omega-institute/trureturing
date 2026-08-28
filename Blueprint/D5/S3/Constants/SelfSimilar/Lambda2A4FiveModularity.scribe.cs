using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.SelfSimilar;

internal sealed class Lambda2A4FiveModularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source Hodge and unimodular-pairing data force both five-modular similarities, "
            + "rank six, and the two recorded discriminant identities.",
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
                        "Here L is the integral span of the fixed ordered wedge basis in the actual "
                            + "second exterior power of the A4 root space. Its form has the displayed "
                            + "Gram matrix, its Hodge operator is the fixed matrix J, and its actual "
                            + "bilinear dual is identified by the concrete map x to Jx divided by five.")),
                    Paragraph(Text(
                        "The Hodge similitude equation makes that dual identification scale the "
                            + "bilinear form by one fifth. It therefore gives similarity ratio "
                            + "one over square root five; the inverse equivalence gives ratio square "
                            + "root five in the other direction.")),
                    Paragraph(Text(
                        "The six-element integral basis supplies rank six. The pairing matrix of "
                            + "the transported dual basis against the source basis is the source's "
                            + "unimodular matrix U, whose determinant is minus one.")),
                    Paragraph(Text(
                        "Changing between the two real bases turns unimodularity into reciprocal "
                            + "source and dual discriminants. Exact five-modular scaling gives the "
                            + "sixth-power determinant scale; reciprocity and positivity then force "
                            + "five raised to six divided by two, hence also five cubed. No "
                            + "precomputed determinant of the fixed Gram matrix enters this chain."))),
                DescribeRole.Theorem))));

    private static Formula FiveModularityFormula()
    {
        Formula form = F.Id("lambda2A4Form");
        Formula lattice = F.Id("lambda2A4Lattice");
        Formula basis = F.Id("lambda2A4IntegralBasis");
        Formula dualEquiv = F.Id("lambda2A4DualEquiv");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula dual = Call("dualSubmodule", form, lattice);
        Formula smallScale = Seq(Frac, Grp(D(1)), Grp(Sqrt, Grp(D(5))));
        Formula largeScale = Seq(Sqrt, Grp(D(5)));
        Formula discriminant = Call("latticeDiscriminant", form, lattice, basis);
        Formula forcedDiscriminant = Seq(
            discriminant, Sp, Eq, Sp, D(5), Caret,
            Grp(Frac, Grp(D(6)), Grp(D(2))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
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
            Open,
            Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, lattice, Comma, Sp,
            Apply(form, Apply(dualEquiv, x), Apply(dualEquiv, y)), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(5)), Sp, Cdot, Sp, Apply(form, x, y), Close,
            Sp, Rightarrow, Sp, forcedDiscriminant, Close, Dot,
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
