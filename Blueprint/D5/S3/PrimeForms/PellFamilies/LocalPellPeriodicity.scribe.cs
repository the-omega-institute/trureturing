using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.PellFamilies;

internal sealed class LocalPellPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula discriminant = F.Id("D");
        Formula unitX = F.Id("x");
        Formula unitY = F.Id("y");
        Formula unitSeed = F.Id("s");
        Formula recurrenceSeed = F.Id("t");
        Formula recurrence = F.Id("G");
        Formula prime = DefinitionDsl.Id("p");
        Formula exponent = DefinitionDsl.Id("k");
        Formula n = DefinitionDsl.Id("n");
        Formula period = F.Id("T");
        Formula index = F.Id("i");
        Formula matrixVariable = F.Id("M");
        Formula vectorVariable = F.Id("v");
        Formula modulus = F.Id("q");
        Formula reduceMatrix = F.Id("R");
        Formula reduceVector = F.Id("r");
        Formula pellMatrix = F.Id("U");
        Formula pellOrbit = F.Id("u");
        Formula recurrenceOrbit = F.Id("z");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula finTwo = Call("Fin", D(2));
        Formula integerVector = Seq(finTwo, Sp, To, Sp, integers);
        Formula integerMatrix = Call("Matrix", finTwo, finTwo, integers);
        Formula modulusDefinition =
            new Formula.Power(prime, exponent);
        Formula matrixReductionDefinition = Seq(
            Open, matrixVariable, Sp, Mapsto, Sp,
            Call("mod", matrixVariable, modulus), Close);
        Formula vectorReductionDefinition = Seq(
            Open, vectorVariable, Sp, Mapsto, Sp, Open, index, Sp, Mapsto, Sp,
            Call("mod", Seq(vectorVariable, Underscore, Grp(index)), modulus),
            Close, Close);
        Formula pellMatrixDefinition = Call("Matrix2", unitX,
            Seq(discriminant, Sp, unitY), unitY, unitX);
        Formula reducedPellMatrix = Call("R", pellMatrix);
        Formula reducedRecurrence = Call("R", recurrence);
        Formula reducedUnitSeed = Call("r", unitSeed);
        Formula reducedRecurrenceSeed = Call("r", recurrenceSeed);
        Formula pellOrbitAt = Seq(pellOrbit, Underscore, Grp(n));
        Formula pellOrbitShift = Seq(
            pellOrbit, Underscore, Grp(n, Plus, period));
        Formula recurrenceOrbitAt = Seq(recurrenceOrbit, Underscore, Grp(n));
        Formula recurrenceOrbitShift = Seq(
            recurrenceOrbit, Underscore, Grp(n, Plus, period));
        Formula pellOrbitDefinition = Seq(
            Open, n, Sp, Mapsto, Sp,
            new Formula.Power(reducedPellMatrix, n), Sp,
            reducedUnitSeed, Close);
        Formula recurrenceOrbitDefinition = Seq(
            Open, n, Sp, Mapsto, Sp,
            new Formula.Power(reducedRecurrence, n), Sp,
            reducedRecurrenceSeed, Close);
        Formula pellUnitCondition = Seq(
            Open,
            new Formula.Power(unitX, D(2)),
            Sp, Minus, Sp, discriminant, Sp,
            new Formula.Power(unitY, D(2)),
            Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            new Formula.Power(unitX, D(2)),
            Sp, Minus, Sp, discriminant, Sp,
            new Formula.Power(unitY, D(2)),
            Sp, Eq, Sp, Minus, D(1), Close);
        Formula unimodularCondition = Seq(
            Open, Call("det", recurrence), Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            Call("det", recurrence), Sp, Eq, Sp, Minus, D(1), Close);
        Formula pellPeriodicity = Seq(
            Exists, Sp, period, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            pellOrbitShift, Sp, Eq, Sp, pellOrbitAt);
        Formula recurrencePeriodicity = Seq(
            Exists, Sp, period, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            recurrenceOrbitShift, Sp, Eq, Sp, recurrenceOrbitAt);
        Formula statement = Disp(Seq(
            Forall, Sp, discriminant, Comma, Sp, unitX, Comma, Sp, unitY,
            Sp, InMacro, Sp, integers, Comma, Sp,
            unitSeed, Comma, Sp, recurrenceSeed, Colon, Sp, integerVector,
            Comma, RowBreak, Grp(), recurrence, Colon, Sp, integerMatrix,
            Comma, Sp, prime, Comma, Sp, exponent, Sp, InMacro, Sp, naturals,
            Comma, Sp, Call("Prime", prime), RowBreak, Grp(), Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            modulus, Sp, Eq, Sp, modulusDefinition, Comma, Sp,
            reduceMatrix, Sp, Eq, Sp, matrixReductionDefinition, Comma,
            RowBreak, Grp(), reduceVector, Sp, Eq, Sp,
            vectorReductionDefinition, Comma, Sp, pellMatrix, Sp, Eq, Sp,
            pellMatrixDefinition, Comma, RowBreak, Grp(),
            pellOrbit, Sp, Eq, Sp, pellOrbitDefinition, Comma, Sp,
            recurrenceOrbit, Sp, Eq, Sp, recurrenceOrbitDefinition, SemiSpace,
            RowBreak, Grp(),
            Open, pellUnitCondition, Sp, Rightarrow, Sp, pellPeriodicity, Close,
            Sp, Land, RowBreak, Grp(),
            Open, unimodularCondition, Sp, Rightarrow, Sp,
            recurrencePeriodicity, Close, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Pell-unit and unimodular recurrences are pure-periodic under every prime-power observation.",
            H("Local Periodicity of Pell Recurrences"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create(
                        "pell-unit-and-unimodular-recurrences-are-locally-periodic"),
                    DeclarationHandle.Create(
                        "D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity."
                            + "pell_unit_and_unimodular_recurrences_are_locally_periodic"),
                    H("Pell recurrences are periodic modulo every prime power"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Fix a prime p and an exponent k. The observer modulus is q = p^k. "
                                + "The displayed reduction maps act entrywise on integral "
                                + "two-by-two matrices and two-coordinate integer states.")),
                        Paragraph(Text(
                            "For an integral Pell unit x + y sqrt(D), multiplication on its two "
                                + "coordinates is the explicit matrix with rows (x, Dy) and "
                                + "(y, x). Its determinant is x^2 - D y^2, so norm one or minus "
                                + "one makes its reduction invertible. The first implication "
                                + "therefore gives a positive pure period for its observed orbit.")),
                        Paragraph(Text(
                            "The second implication treats an arbitrary integral unimodular "
                                + "two-coordinate recurrence independently. Reduction preserves "
                                + "the unit determinant, and the reduced matrix belongs to a "
                                + "finite unit group. Its positive finite order is a period from "
                                + "time zero for every reduced seed."))),
                    DescribeRole.Theorem))));
    }
}
