using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DenseGapMirrorParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula gapCount = F.Id("gapCount");
        Formula offset = F.Id("offset");
        Formula gapCode = F.Id("gapCode");
        Formula index = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula booleans = Call("Bool");
        Formula booleanLists = Call("List", booleans);
        Formula gapIndex = Call("Fin", gapCount);
        Formula pointIndex = Call("Fin", Add(gapCount, Num(1)));
        Formula offsetType = new Formula.TypeArrow(pointIndex, integers);
        Formula GapAt(Formula i) => Subtract(
            Apply(offset, Call("succ", i)),
            Apply(offset, Call("castSucc", i)));

        Formula denseGapPremise = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            gapIndex,
            new Formula.Logic(
                Equal(GapAt(index), Num(2)),
                FormulaLogicOperator.Or,
                Equal(GapAt(index), Num(4))));
        Formula residueReadout = Lambda(
            index,
            pointIndex,
            Call("cast", Apply(offset, index), Call("ZMod", Num(3))));
        Formula modThreePremise = new Formula.Not(
            Call("Surjective", residueReadout));
        Formula premises = new Formula.Logic(
            denseGapPremise, FormulaLogicOperator.And, modThreePremise);

        Formula gapCodeValue = Call(
            "ofFn",
            Lambda(
                index,
                gapIndex,
                Call("decide", Equal(GapAt(index), Num(4)))));
        Formula pointCount = Add(gapCount, Num(1));

        Formula selfMirror = new Formula.Logic(
            Call("Even", pointCount),
            FormulaLogicOperator.Implies,
            Equal(Call("reverse", gapCode), gapCode));
        Formula complementaryMirror = new Formula.Logic(
            Call("Odd", pointCount),
            FormulaLogicOperator.Implies,
            Equal(
                Call("reverse", gapCode),
                Call("map", F.Id("not"), gapCode)));
        Formula conclusions = new Formula.Logic(
            selfMirror, FormulaLogicOperator.And, complementaryMirror);
        Formula body = Seq(
            Let(gapCode, booleanLists, gapCodeValue),
            conclusions);

        Formula statement = Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("gapCount"), naturals),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("offset"), offsetType),
            ],
            new Formula.Logic(premises, FormulaLogicOperator.Implies, body)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Dense admissible integer configurations have parity-controlled reflection.",
            H("Dense Gap Mirror Parity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("dense-gap-mirror-parity"),
                    DeclarationHandle.Create(
                        "D5/S3/Arith/Congruence/DenseGapMirrorParity.dense_gap_mirror_parity"),
                    H("Point-count parity determines the reflected gap code"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The configuration has gapCount plus one ordered integer offsets. "
                                + "Every adjacent gap is two or four, and the offsets do not "
                                + "cover every residue modulo three.")),
                        Paragraph(Text(
                            "The Boolean gap code is constructed by recording four-gaps as true. "
                                + "Mod-three admissibility forces alternation; reflection fixes "
                                + "the code at even point count and complements it at odd count."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Comma, Sp);
}
