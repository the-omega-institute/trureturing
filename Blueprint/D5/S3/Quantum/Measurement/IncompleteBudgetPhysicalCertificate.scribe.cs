using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class IncompleteBudgetPhysicalCertificateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate."
            + "incomplete_budget_physical_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero invisible Hermitian direction gives an explicit physical readout certificate.",
        H("Incomplete Budget Physical Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("incomplete-budget-physical-certificate"),
            DeclarationHandle.Create(Declaration),
            H("An invisible direction yields two indistinguishable physical states"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The visible space is constructed from the identity and the declared "
                        + "positive effects. The supplied nonzero Hermitian direction lies "
                        + "in its Hilbert--Schmidt orthogonal residual.")),
                Paragraph(Text(
                    "A norm-controlled positive epsilon perturbs the maximally mixed state "
                        + "in both directions. The public statement records positivity, both "
                        + "trace-one identities, distinction, and equality of every declared "
                        + "Born readout."))),
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

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("A"), effects = F.Id("E");
        Formula i = F.Id("i"), effect = F.Id("F"), direction = F.Id("D");
        Formula epsilon = F.Id("epsilon"), visible = F.Id("V"), residual = F.Id("N");
        Formula rhoPlus = new Formula.Subscript(F.Id("rho"), Plus);
        Formula rhoMinus = new Formula.Subscript(F.Id("rho"), Minus);
        Formula nat = F.Id("Nat"), type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula hermitian = Call("HermitianSpace", d);
        Formula matrix = Call("Matrix", Call("Fin", d), Call("Fin", d), complex);
        Formula effectMatrix = Call("matrix", effect);
        Formula effectType = Seq(
            OpenBrace, effect, Colon, Sp, hermitian, Sp, Mid, Sp,
            Call("PosSemidef", effectMatrix), Sp, Land, Sp,
            Call("PosSemidef", Seq(D(1), Sp, Minus, Sp, effectMatrix)), CloseBrace);
        Formula effectAt = Apply(effects, i);
        Formula effectAtHermitian = Call("hermitian", effectAt);
        Formula effectAtMatrix = Call("matrix", effectAt);
        Formula directionMatrix = Call("matrix", direction);
        Formula effectRange = Seq(
            OpenBrace, effectAtHermitian, Colon, Sp, i, Sp, InMacro, Sp, indexType,
            CloseBrace);
        Formula visibleDefinition = Equal(
            visible,
            Call("span", real,
                Call("insert", Call("identityHermitian", d), effectRange)));
        Formula residualDefinition = Equal(residual, Call("orthogonal", visible));
        Formula premise = And(
            Seq(direction, Sp, InMacro, Sp, residual),
            new Formula.Relation(direction, FormulaRelationOperator.NotEqual, D(0)));
        Formula inverseDimension = Call("inv", Call("complex", d));
        Formula identity = Call("identityMatrix", d);
        Formula epsilonComplex = Call("complex", epsilon);
        Formula plusDefinition = Seq(
            Multiply(inverseDimension, identity), Sp, Plus, Sp,
            Multiply(epsilonComplex, directionMatrix));
        Formula minusDefinition = Seq(
            Multiply(inverseDimension, identity), Sp, Minus, Sp,
            Multiply(epsilonComplex, directionMatrix));
        Formula positivePlus = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThanOrEqual,
            Call("ofMatrix", rhoPlus));
        Formula positiveMinus = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThanOrEqual,
            Call("ofMatrix", rhoMinus));
        Formula tracePlus = Equal(Call("Tr", rhoPlus), D(1));
        Formula traceMinus = Equal(Call("Tr", rhoMinus), D(1));
        Formula distinct = new Formula.Relation(
            rhoPlus, FormulaRelationOperator.NotEqual, rhoMinus);
        Formula readoutEquality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), indexType)],
            Equal(
                Call("Tr", Multiply(rhoPlus, effectAtMatrix)),
                Call("Tr", Multiply(rhoMinus, effectAtMatrix))));
        Formula certificate = And(
            positivePlus,
            And(positiveMinus,
                And(tracePlus,
                    And(traceMinus,
                        And(distinct, readoutEquality)))));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak, Grp(),
            indexType, Colon, Sp, type, Comma, RowBreak, Grp(),
            effects, Colon, Sp, indexType, Sp, To, Sp, effectType, Comma,
            RowBreak, Grp(),
            direction, Colon, Sp, hermitian, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            visibleDefinition, Comma, Sp, residualDefinition, Semi, RowBreak, Grp(),
            Open, premise, Close, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, epsilon, Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            rhoPlus, Colon, Sp, matrix, Sp, Eq, Sp,
            plusDefinition, Comma, RowBreak, Grp(),
            rhoMinus, Colon, Sp, matrix, Sp, Eq, Sp,
            minusDefinition, Semi, RowBreak, Grp(),
            certificate, Dot));
    }
}
