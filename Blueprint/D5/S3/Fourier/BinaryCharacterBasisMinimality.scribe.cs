using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class BinaryCharacterBasisMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary-character bases are exactly minimum complete observation families.",
        H("Binary Character Basis Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-character-basis-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/BinaryCharacterBasisMinimality."
                        + "binary_character_basis_minimality"),
                H("Character-span bases are minimum complete observation families"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be a finite abelian group. Binary characters are represented "
                            + "additively as linear functionals on the canonical quotient of G "
                            + "by doubles, so evaluation remains on the original group through "
                            + "the canonical quotient map.")),
                    Paragraph(Text(
                        "The character space H is constructed as the binary-field span of the "
                            + "given character family, and r is its finite dimension. The "
                            + "displayed same-kernel premise is pointwise on G, not an abstract "
                            + "replacement definition of sufficiency.")),
                    Paragraph(Text(
                        "The minimum same-span cardinality is inherited from the frozen binary "
                            + "role theorem. Equality of actual joint kernels forces the "
                            + "competitor span to equal H, giving the lower bound r.")),
                    Paragraph(Text(
                        "A linearly independent Fin(r)-indexed family is extracted from the "
                            + "original characters, spans H, and has their joint kernel. The "
                            + "last public clause quantifies over an arbitrary supplied basis of "
                            + "H and proves both kernel sufficiency and minimum cardinality."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula originalIndex = F.Id("I");
        Formula competitorIndex = F.Id("J");
        Formula basisIndex = F.Id("B");
        Formula characters = F.Id("chi");
        Formula competitor = F.Id("psi");
        Formula basis = F.Id("beta");
        Formula selected = F.Id("sigma");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula originalSet = Call("range", characters);
        Formula characterSpan = F.Id("H");
        Formula originalSpan = Call("span", field, originalSet);
        Formula rank = F.Id("r");
        Formula quotientPoint(Formula g) => Call("mkQ", D(2), g);
        Formula Evaluate(Formula family, Formula index, Formula g) =>
            Apply(Apply(family, index), quotientPoint(g));
        Formula JointZero(
            Formula family,
            Formula index,
            Formula indexType,
            Formula g) => Seq(
                Forall, Sp, index, Sp, InMacro, Sp, indexType, Comma, Sp,
                Evaluate(family, index, g), Sp, Eq, Sp, D(0));

        Formula g = F.Id("g");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula sameJointKernel = Seq(
            Forall, Sp, g, Sp, InMacro, Sp, group, Comma, Sp,
            Open, JointZero(characters, i, originalIndex, g), Close,
            Sp, Iff, Sp,
            Open, JointZero(competitor, j, competitorIndex, g), Close);

        Formula cardinality = F.Id("kappa");
        Formula chosen = F.Id("S");
        Formula admissibleCardinalities = Seq(
            OpenBrace, cardinality, Sp, Mid, Sp,
            Exists, Sp, chosen, Comma, Sp,
            chosen, Sp, Subseteq, Sp, originalSet, Sp, Land, Sp,
            Call("span", field, chosen), Sp, Eq, Sp, characterSpan, Sp, Land, Sp,
            Call("card", chosen), Sp, Eq, Sp, cardinality,
            CloseBrace);
        Formula minimumClause = Call(
            "IsLeast",
            admissibleCardinalities,
            Call("rank", field, characterSpan));

        Formula selectedType = Seq(Call("Fin", rank), Sp, To, Sp, dual);
        Formula selectedFromOriginal = Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Call("Fin", rank), Comma, Sp,
            Apply(selected, k), Sp, InMacro, Sp, originalSet);
        Formula selectedKernel = Seq(
            Forall, Sp, g, Sp, InMacro, Sp, group, Comma, Sp,
            Open, JointZero(selected, k, Call("Fin", rank), g), Close,
            Sp, Iff, Sp,
            Open, JointZero(characters, i, originalIndex, g), Close);
        Formula basisKernel = Seq(
            Forall, Sp, g, Sp, InMacro, Sp, group, Comma, Sp,
            Open, JointZero(basis, j, basisIndex, g), Close,
            Sp, Iff, Sp,
            Open, JointZero(characters, i, originalIndex, g), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, originalIndex, Comma, Sp,
            competitorIndex, Comma, Sp, basisIndex, Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Finite", group), Comma, Sp,
            Typeclass("Finite", originalIndex), Comma, RowBreak, Grp(),
            Typeclass("Fintype", competitorIndex), Comma, Sp,
            Typeclass("Fintype", basisIndex), Comma, RowBreak, Grp(),
            characters, Colon, Sp, originalIndex, Sp, To, Sp, dual, Comma, Sp,
            competitor, Colon, Sp, competitorIndex, Sp, To, Sp, dual,
            Comma, RowBreak, Grp(),
            characterSpan, Sp, Colon, Eq, Sp,
            originalSpan, Comma, Sp,
            rank, Sp, Colon, Eq, Sp,
            Call("finrank", field, characterSpan), Comma, RowBreak, Grp(),
            basis, Colon, Sp, Call("Basis", basisIndex, field, characterSpan),
            Comma, RowBreak, Grp(),
            Open, sameJointKernel, Close, Sp, Rightarrow, RowBreak, Grp(),
            minimumClause, Sp, Land, Sp,
            rank, Sp, Leq, Sp, Call("card", competitorIndex), Sp, Land,
            RowBreak, Grp(),
            Open, Exists, Sp, selected, Colon, Sp, selectedType, Comma, Sp,
            Open, selectedFromOriginal, Close, Sp, Land, Sp,
            Call("LinearIndependent", field, selected), Sp, Land,
            RowBreak, Grp(),
            Call("span", field, Call("range", selected)), Sp, Eq, Sp,
            characterSpan, Sp, Land, Sp, selectedKernel, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Open, basisKernel, Close, Sp, Land, Sp,
            Call("card", basisIndex), Sp, Leq, Sp,
            Call("card", competitorIndex), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
