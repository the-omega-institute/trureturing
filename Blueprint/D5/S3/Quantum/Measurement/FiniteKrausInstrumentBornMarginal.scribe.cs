using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteKrausInstrumentBornMarginalDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal."
            + "finite_kraus_instrument_born_marginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite normalized Kraus instruments have the expected one-step Born marginal.",
        H("Finite Kraus Instrument Born Marginal"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-instrument-born-marginal"),
            DeclarationHandle.Create(Declaration),
            H("A finite Kraus branch has the Born weight of its effect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public Kraus family is normalized at every setting, so its "
                        + "outcome branches form a finite-dimensional instrument. The input "
                        + "uses the canonical positive trace-one density-state carrier.")),
                Paragraph(Text(
                    "Each branch and effect is constructed by a finite Kraus sum. Trace "
                        + "linearity and cyclicity move the outer Kraus operator across the "
                        + "trace, yielding the canonical Born trace pairing."))),
            DescribeRole.Theorem))));

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula system = F.Id("n"), settingType = F.Id("X");
        Formula outcomeType = F.Id("A"), krausType = F.Id("R");
        Formula family = F.Id("K"), state = Rho, x = F.Id("x");
        Formula outcome = F.Id("a"), k = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", system, system, complex);
        Formula krausAt = Apply(family, x, outcome, k);
        Formula stateValue = F.Id("S");
        Formula branchMatrix = F.Id("B");
        Formula effectMatrix = F.Id("E");
        Formula stateDefinition = Call("matrix", state);
        Formula krausProduct = Multiply(Call("star", krausAt), krausAt);
        Formula normalized = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), settingType)],
            Equal(
                Seq(Sum, Underscore, Grp(outcome, Sp, InMacro, Sp, outcomeType), Sp,
                    Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
                    krausProduct),
                Call("identityMatrix", system)));
        Formula familyFunctionType = Seq(
            settingType, Sp, To, Sp, outcomeType, Sp, To, Sp,
            krausType, Sp, To, Sp, matrix);
        Formula instrumentType = Seq(
            OpenBrace, family, Colon, Sp, familyFunctionType, Sp, Mid, Sp,
            normalized, CloseBrace);
        Formula branchDefinition = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
            Multiply(Multiply(krausAt, stateValue), Call("star", krausAt)));
        Formula effectDefinition = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
            krausProduct);
        Formula marginal = Equal(
            Call("Tr", branchMatrix),
            Call("bornProbability", stateValue, effectMatrix));

        return Disp(Seq(
            Forall, Sp,
            system, Comma, Sp, settingType, Comma, Sp,
            outcomeType, Comma, Sp, krausType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("Fintype", system), Comma, Sp,
            Call("Nonempty", system), Comma, Sp,
            Call("DecidableEq", system), Comma, RowBreak, Grp(),
            Call("Fintype", outcomeType), Comma, Sp,
            Call("Fintype", krausType), Comma, RowBreak, Grp(),
            family, Colon, Sp, instrumentType, Comma, RowBreak, Grp(),
            state, Colon, Sp, Call("DensityState", system), Comma, RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, settingType, Comma, Sp,
            outcome, Colon, Sp, outcomeType, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            stateValue, Colon, Sp, matrix, Sp, Eq, Sp,
            stateDefinition, Comma, RowBreak, Grp(),
            branchMatrix, Colon, Sp, matrix, Sp, Eq, Sp,
            branchDefinition, Comma, RowBreak, Grp(),
            effectMatrix, Colon, Sp, matrix, Sp, Eq, Sp,
            effectDefinition, Semi, RowBreak, Grp(),
            marginal, Dot));
    }
}
