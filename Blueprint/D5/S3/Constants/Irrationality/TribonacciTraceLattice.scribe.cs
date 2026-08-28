using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TribonacciTraceLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var naturals = Id("N");
        var integers = Id("Z");
        var complex = Id("C");
        var pairType = Call("Prod", naturals, naturals);
        var v1 = Id("v1");
        var v2 = Id("v2");
        var pair = Id("pair");
        var k = Id("k");
        var z = Id("z");
        var t = Id("tribonacciConstant");

        Formula And(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right);
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula Le(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
        Formula Lt(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
        Formula Member(Formula value, Formula carrier) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, carrier);

        var scanCondition = And(
            Le(Num(1), v1),
            And(Le(v1, v2), Le(v2, Num(200))));
        var scanBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("v1"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("v2"), naturals),
            ],
            Implies(
                scanCondition,
                Lt(
                    new Formula.Absolute(Call("tribonacciDeficit", v1, v2)),
                    new Formula.Fraction(Num(955), Num(1000)))));

        var scanCount = Equal(
            Call("card", Id("tribonacciNonintegralScanPairs")),
            Num(8934));
        var ratio = new Formula.Fraction(Num(8934), Num(20100));
        var percentageInterval = And(
            Le(new Formula.Fraction(Num(4435), Num(10000)), ratio),
            Lt(ratio, new Formula.Fraction(Num(4445), Num(10000))));
        var countAndPercentage = And(scanCount, percentageInterval);

        var exactSpectrum = Equal(
            Call(
                "image",
                Id("tribonacciDeficitCodeAt10"),
                Id("tribonacciScanPairs")),
            Id("tribonacciScanSpectrum"));

        var pairV1 = Call("fst", pair);
        var pairV2 = Call("snd", pair);
        var deficitCode = Call("tribonacciDeficitCodeAt", Num(10), pairV1, pairV2);
        var conjugatePairTrace = Call("tribonacciConjugatePairTrace", deficitCode);
        var integerCongruence = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("pair"), pairType)],
            Implies(
                Member(pair, Id("tribonacciNonintegralScanPairs")),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [new Formula.BoundVariable(FormulaIdentifier.Create("k"), integers)],
                    Equal(
                        Call("tribonacciDeficit", pairV1, pairV2),
                        Subtract(k, conjugatePairTrace)))));

        var quadraticDeficit = Call("deficit", v1, v2);
        var quadraticClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("v1"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("v2"), naturals),
            ],
            And(
                Equal(
                    quadraticDeficit,
                    Call("deficitContraction", v1, v2)),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [new Formula.BoundVariable(FormulaIdentifier.Create("z"), integers)],
                    Equal(quadraticDeficit, z))));

        var cubicFactorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("z"), complex)],
            Equal(
                Subtract(
                    Subtract(
                        Subtract(
                            new Formula.Power(z, Num(3)),
                            new Formula.Power(z, Num(2))),
                        z),
                    Num(1)),
                Multiply(
                    Subtract(z, t),
                    Call("conjugateCofactor", z))));
        var cubicObstruction = Call("Irrational", Subtract(Num(1), t));
        var cubicClause = And(cubicFactorization, cubicObstruction);
        var privilegeClause = And(quadraticClause, cubicObstruction);

        var statement = And(
            scanBound,
            And(
                countAndPercentage,
                And(
                    exactSpectrum,
                    And(
                        integerCongruence,
                        And(quadraticClause, And(cubicClause, privilegeClause))))));

        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TribonacciTraceLattice.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "On the certified Tribonacci scan, the nonintegral discrete spectrum is a conjugate-pair trace lattice.",
            H("Tribonacci Trace Lattice"),
            Blocks(
                Paragraph(Text(
                    "For the triangular window 1 <= v1 <= v2 <= 200, every deficit has "
                        + "absolute value strictly below 955/1000. Exactly 8,934 of the 20,100 "
                        + "pairs are nonintegral, and the exact ratio lies in the half-open "
                        + "rounding interval [0.4435, 0.4445), hence rounds to 44.4 percent. "
                        + "The cubic-code image of that same scan is exactly the frozen "
                        + "eight-point spectrum.")),
                Paragraph(Text(
                    "For each pair in the nonintegral scan, let w be its exact cubic deficit "
                        + "code evaluated at the upper non-Perron Tribonacci root. There is an "
                        + "integer k such that the real deficit equals k minus w plus its "
                        + "complex conjugate in parentheses: deficit = k - (w + conj(w)). "
                        + "Thus modulo the integers the deficit is the negative C/R trace of "
                        + "the genuinely distinct complex-conjugate pair.")),
                Paragraph(Text(
                    "The remaining conjunctions retain the structural contrast verbatim. On "
                        + "the quadratic side the expanding and contracting deficits agree and "
                        + "the deficit is integral. On the cubic side the characteristic cubic "
                        + "splits into the Perron factor and its quadratic cofactor, while one "
                        + "minus the Perron root is irrational, so the Perron root alone does "
                        + "not carry the trace. Their conjunction states that integrality is a "
                        + "privilege of the two-faced structure.")),
                Paragraph(Text(
                    "The numerical bound, count, percentage, spectrum, and trace-lattice "
                        + "identification are window-certificate statements. They make no "
                        + "claim about an unrestricted scan or all natural index pairs.")),
                Describe.Lean(
                    DescribeId.Create("pzg-remark-six-twenty-seven-tribonacci-trace-lattice"),
                    DeclarationHandle.Create(
                        declarationPrefix + "pzg_remark_6_27_tribonacci_trace_lattice"),
                    H("PZG Remark 6.27: the Tribonacci trace lattice"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This one declaration packages all thirteen independently projectable "
                            + "proposition leaves. Frozen scan and structural certificates are "
                            + "referenced; the new leaf is the integer-congruence identity for "
                            + "the complex-conjugate pair trace."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/CubicConjugateTrace")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TwoFacedPrivilege")),
            ]));
    }
}
