using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class SymmetricOffLineQuarticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A centered quartic has full reflection and conjugation symmetry while all four zeros remain off the critical line.",
        H("Symmetric Off-Line Quartic"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-symmetry-does-not-force-critical-line-localization"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic."
                    + "symmetric_off_line_quartic_spec"),
            H("Full symmetry does not force critical-line localization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For arbitrary nonzero real transverse and vertical parameters, the displayed "
                        + "centered quartic is complex differentiable everywhere. Its zeros are "
                        + "exactly the four independent sign choices, and the nonzero hypotheses "
                        + "make those four points distinct.")),
                Paragraph(Text(
                    "Evaluation is invariant under s mapped to one minus s and is covariant under "
                        + "complex conjugation. Nevertheless every zero has real part different "
                        + "from the critical abscissa, and an explicit root refutes universal "
                        + "fixed-line localization for this same polynomial."))),
            DescribeRole.Theorem)),
        []));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LambdaExpr(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula s = F.Id("s");
        Formula x = F.Id("X");
        Formula centered = F.Id("centered");
        Formula critical = Call("criticalAbscissa");
        Formula quartic = new Formula.Subscript(F.Id("P"), Seq(delta, Comma, gamma));
        Formula imaginary = F.Id("i");

        Formula centeredDefinition = Seq(x, Sp, Minus, Sp, Call("C", critical));
        Formula gammaSquare = Square(Call("C", gamma));
        Formula leftQuadratic = Seq(
            Square(Seq(centered, Sp, Minus, Sp, Call("C", delta))),
            Sp, Plus, Sp, gammaSquare);
        Formula rightQuadratic = Seq(
            Square(Seq(centered, Sp, Plus, Sp, Call("C", delta))),
            Sp, Plus, Sp, gammaSquare);
        Formula quarticDefinition = Seq(
            Open, leftQuadratic, Close, Sp, Times, Sp,
            Open, rightQuadratic, Close);

        Formula upperRight = Seq(
            critical, Sp, Plus, Sp, delta, Sp, Plus, Sp,
            imaginary, Sp, Times, Sp, gamma);
        Formula lowerRight = Seq(
            critical, Sp, Plus, Sp, delta, Sp, Minus, Sp,
            imaginary, Sp, Times, Sp, gamma);
        Formula upperLeft = Seq(
            critical, Sp, Minus, Sp, delta, Sp, Plus, Sp,
            imaginary, Sp, Times, Sp, gamma);
        Formula lowerLeft = Seq(
            critical, Sp, Minus, Sp, delta, Sp, Minus, Sp,
            imaginary, Sp, Times, Sp, gamma);
        Formula rootSet = Seq(
            OpenBrace, upperRight, Comma, Sp, lowerRight, Comma, Sp,
            upperLeft, Comma, Sp, lowerLeft, CloseBrace);
        Formula evaluated = Call("eval", quartic, s);

        Formula entireClause = Call(
            "Differentiable", complex, LambdaExpr(s, evaluated));
        Formula exactRootsClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            new Formula.Logic(
                EqualTo(evaluated, D(0)),
                FormulaLogicOperator.Iff,
                Seq(s, Sp, InMacro, Sp, rootSet)));
        Formula cardinalityClause = EqualTo(Call("card", rootSet), D(4));
        Formula reflectionClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            EqualTo(
                Call("eval", quartic, Seq(D(1), Sp, Minus, Sp, s)),
                evaluated));
        Formula conjugationClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            EqualTo(
                Call("eval", quartic, Call("conj", s)),
                Call("conj", evaluated)));
        Formula zeroPremise = EqualTo(evaluated, D(0));
        Formula offLineClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(zeroPremise, NotEqualTo(Call("Re", s), critical)));
        Formula nonLocalizationClause = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(zeroPremise, EqualTo(Call("Re", s), critical))));
        Formula conclusion = And(
            entireClause,
            And(
                exactRootsClause,
                And(
                    cardinalityClause,
                    And(
                        reflectionClause,
                        And(
                            conjugationClause,
                            And(offLineClause, nonLocalizationClause))))));

        return Disp(Seq(
            Forall, Sp, delta, Comma, Sp, gamma, Sp, InMacro, Sp, real,
            Comma, RowBreak, Grp(),
            Open, NotEqualTo(delta, D(0)), Sp, Land, Sp,
            NotEqualTo(gamma, D(0)), Close, Sp, Rightarrow,
            RowBreak, Grp(), Operatorname, Grp(F.Id("let")), Sp,
            centered, Sp, Colon, Eq, Sp, centeredDefinition, Comma,
            RowBreak, Grp(), Operatorname, Grp(F.Id("let")), Sp,
            quartic, Sp, Colon, Eq, Sp, quarticDefinition, Comma,
            RowBreak, Grp(), conclusion, Dot));
    }
}
