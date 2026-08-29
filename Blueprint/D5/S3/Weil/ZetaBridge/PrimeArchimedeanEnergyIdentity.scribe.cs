using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PrimeArchimedeanEnergyIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-side Weil form is boundary energy plus continuous and arithmetic jump "
            + "energies minus the coherent mass threshold.",
        H("Prime-Archimedean Energy Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-archimedean-energy-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity."
                        + "prime_archimedean_energy_identity"),
                H("Prime-Archimedean energy identity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Z is the frozen multiplicity-aware nontrivial-zero enumeration, while f "
                            + "is an even smooth compactly supported complex test function. The "
                            + "support, symmetric zero convergence, and Archimedean convergence "
                            + "witnesses are exactly those consumed by the explicit formula.")),
                    Paragraph(Text(
                        "The boundary term is twice the squared modulus of the one-half "
                            + "Fourier-Laplace observation. The remaining positive terms are the "
                            + "canonical continuous Archimedean jump energy and the finite "
                            + "prime-power translation energy.")),
                    Paragraph(Text(
                        "The first public conjunct is the exact complex zero-side identity. The "
                            + "second states that zero-side nonnegativity is equivalent to the "
                            + "displayed Prime-Archimedean Poincare inequality."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula variable = F.Id("x");
        Formula supportWitness = F.Id("hSupport");
        Formula zeroWitness = F.Id("hZero");
        Formula archWitness = F.Id("hArch");
        Formula convolutionSquare = Call("convolutionSquare", test);
        Formula zeroSide = Call("zeroSum", zeros, convolutionSquare, zeroWitness);
        Formula supportInterval = Seq(
            OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket);
        Formula boundaryReadout = Seq(
            Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            Call("exp", Seq(Frac, Grp(variable), Grp(D(2)))), Sp,
            Call("f", variable), Sp, F.Id("d"), variable);
        Formula boundaryEnergy = Seq(
            D(2), Sp, Lvert, boundaryReadout, Rvert, Caret, Grp(D(2)));
        Formula archEnergy = Call("archimedeanJumpEnergy", test);
        Formula arithmeticEnergy = Call("arithmeticJumpEnergy", scale, test);
        Formula totalEnergy = new Formula.Binary(
            new Formula.Binary(
                boundaryEnergy,
                FormulaBinaryOperator.Add,
                archEnergy),
            FormulaBinaryOperator.Add,
            arithmeticEnergy);
        Formula thresholdCoefficient = new Formula.Binary(
            new Formula.Binary(
                D(2),
                FormulaBinaryOperator.Multiply,
                Call("totalPrimeWeight", scale)),
            FormulaBinaryOperator.Subtract,
            Seq(Operatorname, Grp(F.Id("archimedeanConstant"))));
        Formula threshold = new Formula.Binary(
            thresholdCoefficient,
            FormulaBinaryOperator.Multiply,
            Call("l2Mass", test));
        Formula identity = new Formula.Relation(
            zeroSide,
            FormulaRelationOperator.Equal,
            new Formula.Binary(totalEnergy, FormulaBinaryOperator.Subtract, threshold));
        Formula positivity = new Formula.Logic(
            new Formula.Relation(
                D(0),
                FormulaRelationOperator.LessThanOrEqual,
                Seq(Re, Open, zeroSide, Close)),
            FormulaLogicOperator.Iff,
            new Formula.Relation(
                threshold,
                FormulaRelationOperator.LessThanOrEqual,
                totalEnergy));
        Formula conclusion = new Formula.Logic(
            identity, FormulaLogicOperator.And, positivity);

        return Disp(Seq(
            Forall, Sp, zeros, Colon, Sp,
            Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            scale, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            supportWitness, Colon, Sp,
            Call("tsupport", test), Sp, Subseteq, Sp, supportInterval, Comma, Sp,
            zeroWitness, Colon, Sp,
            Call("SymmetricConvergent", zeros, convolutionSquare), Comma, Sp,
            archWitness, Colon, Sp,
            Call("ArchimedeanConvergent", convolutionSquare),
            Sp, Rightarrow, Sp, conclusion));
    }
}
