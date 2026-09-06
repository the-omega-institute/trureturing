using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class SkolemOrderFiveModularExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A certified period-thirty-one parity orbit excludes zeros in sixteen residue classes "
            + "for an infinite congruence class of order-five integer recurrences.",
        H("Order-Five Skolem Modular Exclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skolem-order-five-state"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.State"),
                H("Five-coordinate parity state"),
                StatementSource.FromAuthor(StateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "State has exactly five coordinates, each valued in ZMod(2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-step"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.step"),
                H("Parity companion step"),
                StatementSource.FromAuthor(StepFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The step shifts four coordinates and adds the old zeroth and third "
                        + "coordinates in the final position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-coefficient-bits"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.coeffBits"),
                H("Prescribed coefficient residues"),
                StatementSource.FromAuthor(CoefficientBitsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five recurrence coefficients reduce to the displayed bit vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-initial-bits"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialBits"),
                H("Prescribed initial residues"),
                StatementSource.FromAuthor(InitialBitsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first five sequence terms reduce to the displayed bit vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-initial-state"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialState"),
                H("Initial parity state"),
                StatementSource.FromAuthor(InitialStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The parity orbit begins at the state represented by the initial residues."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-integer-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.intRecurrence"),
                H("Order-five integer recurrence"),
                StatementSource.FromAuthor(IntRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The recurrence has order five and coefficient function a. Its IsSolution "
                        + "equation is the order-five recurrence from the candidate atom."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-reduced-state"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.reducedState"),
                H("Coordinatewise parity reduction"),
                StatementSource.FromAuthor(ReducedStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Five consecutive integer terms are cast coordinatewise to ZMod(2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-orbit-state"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbitState"),
                H("Binary companion orbit"),
                StatementSource.FromAuthor(OrbitStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nth orbit state is the nth iterate of step at the prescribed initial "
                        + "state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-possible-zero-residues"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.possibleZeroResidues"),
                H("Possible zero residues modulo thirty-one"),
                StatementSource.FromAuthor(PossibleZeroResiduesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the full fifteen-element exceptional residue set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-reduction-commutes-with-step"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion."
                        + "reduction_commutes_with_step"),
                H("Reduction modulo two commutes with the companion step"),
                StatementSource.FromAuthor(ReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For E_a of order five with coefficients a, reducedState(u,n) is the five-tuple "
                        + "of terms u_n through u_(n+4), each cast to ZMod(2). Under the "
                        + "displayed coefficient congruence, the IsSolution equation reduces "
                        + "its final coordinate to x_0+x_3, uniformly for every integer lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-orbit-closes"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_closes"),
                H("The binary state orbit closes after thirty-one steps"),
                StatementSource.FromAuthor(OrbitClosesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here s_0=(1,0,0,0,0) in ZMod(2)^5 and step sends "
                        + "(x_0,x_1,x_2,x_3,x_4) to (x_1,x_2,x_3,x_4,x_0+x_3). "
                        + "Ordinary kernel decision checks the closing edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-orbit-no-early-return"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion."
                        + "orbit_no_early_return"),
                H("The binary state orbit has no early return"),
                StatementSource.FromAuthor(NoEarlyReturnFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ordinary kernel decision checks every positive iterate from one through "
                        + "thirty. Together with the closing edge, this certifies exact period "
                        + "thirty-one rather than merely a period dividing thirty-one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-orbit-nonzero-readoff"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion."
                        + "orbit_nonzero_readoff"),
                H("The first coordinate is one on the sixteen complementary residues"),
                StatementSource.FromAuthor(OrbitReadoffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exceptional set Z is exactly "
                        + "{1,2,3,4,6,8,12,15,16,17,23,24,27,29,30}. Ordinary kernel "
                        + "decision reads the first coordinate on every residue outside Z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-odd-outside-exceptional-residues"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion."
                        + "odd_of_mod31_not_mem"),
                H("Every term outside the exceptional residues is odd"),
                StatementSource.FromAuthor(OddnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The commuting reduction identifies every lifted solution state with the "
                        + "certified binary orbit. IsPeriodicPt.iterate_mod_apply reduces n by "
                        + "the natural-number remainder modulo thirty-one, and the readout "
                        + "certificate makes the corresponding integer term odd."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skolem-order-five-uniform-modular-exclusion"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/SkolemOrderFiveModularExclusion."
                        + "zero_index_mod31_mem"),
                H("Uniform modular exclusion for order-five integer recurrences"),
                StatementSource.FromAuthor(WholeAtomFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct is the uniform oddness statement on all sixteen "
                            + "complementary residue classes. The second is its zero-index "
                            + "consequence, so this single theorem states the whole candidate "
                            + "atom rather than covering only its final corollary.")),
                    Paragraph(Text(
                        "The symbol n mod 31 denotes the natural-number remainder, represented "
                            + "by modulo notation rather than a fraction. This theorem does not "
                            + "decide whether a zero occurs in any of the fifteen exceptional "
                            + "classes and is not a decision procedure for the order-five "
                            + "Skolem problem."))),
                DescribeRole.Theorem))));

    private static Formula StateFormula()
    {
        Formula modTwo = Call("ZMod", D(2));
        return Disp(Seq(
            Named("State"), Sp, Eq, Sp,
            Parenthesized(Joined([
                Seq(F.Id("x0"), Colon, Sp, modTwo),
                Seq(F.Id("x1"), Colon, Sp, modTwo),
                Seq(F.Id("x2"), Colon, Sp, modTwo),
                Seq(F.Id("x3"), Colon, Sp, modTwo),
                Seq(F.Id("x4"), Colon, Sp, modTwo),
            ], Comma)), Dot));
    }

    private static Formula StepFormula()
    {
        Formula s = F.Id("s");
        return Disp(Seq(
            Forall, Sp, s, Colon, Sp, Named("State"), Comma, Sp,
            Equal(
                Call("step", s),
                Tuple(
                    Projection(s, "x1"),
                    Projection(s, "x2"),
                    Projection(s, "x3"),
                    Projection(s, "x4"),
                    Sum(Projection(s, "x0"), Projection(s, "x3")))),
            Dot));
    }

    private static Formula CoefficientBitsFormula() =>
        Disp(Seq(
            Equal(Named("coeffBits"), Tuple(D(1), D(0), D(0), D(1), D(0))), Dot));

    private static Formula InitialBitsFormula() =>
        Disp(Seq(
            Equal(Named("initialBits"), Tuple(D(1), D(0), D(0), D(0), D(0))), Dot));

    private static Formula InitialStateFormula() =>
        Disp(Seq(Equal(Named("initialState"), InitialState()), Dot));

    private static Formula IntRecurrenceFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");
        Formula m = F.Id("m");
        Formula i = F.Id("i");
        Formula recurrence = Recurrence(a);
        Formula summand = new Formula.Binary(
            Sub(a, i),
            FormulaBinaryOperator.Multiply,
            Sub(u, Sum(m, Call("val", i))));
        Formula finiteSum = Seq(
            new Formula.Subscript(
                F.Sum,
                Seq(i, Sp, InMacro, Sp, Call("Fin", D(5)))),
            Sp,
            summand);

        return Disp(new Formula.Aligned([
            ParameterRow(a, u),
            Seq(
                Equal(Projection(recurrence, "order"), D(5)), Sp, Land, Sp,
                Equal(Projection(recurrence, "coeffs"), a), Comma),
            Seq(Parenthesized(IsSolution(a, u)), Sp, Leftrightarrow),
            Seq(
                Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                Equal(Sub(u, Sum(m, D(5))), finiteSum), Dot),
        ]));
    }

    private static Formula ReducedStateFormula()
    {
        Formula u = F.Id("u");
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, u, Colon, Sp, FunctionType(Naturals(), Integers()),
            Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Equal(
                Call("reducedState", u, n),
                Tuple(
                    CastModTwo(Sub(u, n)),
                    CastModTwo(Sub(u, Sum(n, D(1)))),
                    CastModTwo(Sub(u, Sum(n, D(2)))),
                    CastModTwo(Sub(u, Sum(n, D(3)))),
                    CastModTwo(Sub(u, Sum(n, D(4)))))),
            Dot));
    }

    private static Formula OrbitStateFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Equal(Call("orbitState", n), Iterate(n)), Dot));
    }

    private static Formula PossibleZeroResiduesFormula() =>
        Disp(Seq(Equal(Named("possibleZeroResidues"), ExceptionalSet()), Dot));

    private static Formula ReductionFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");
        Formula n = F.Id("n");
        Formula conclusion = Equal(
            Call("reducedState", u, Sum(n, D(1))),
            Call("step", Call("reducedState", u, n)));

        return Disp(new Formula.Aligned([
            ParameterRow(a, u),
            Seq(Parenthesized(IsSolution(a, u)), Sp, Rightarrow),
            Seq(Parenthesized(CoefficientCongruence(a)), Sp, Rightarrow),
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp, conclusion, Dot),
        ]));
    }

    private static Formula OrbitClosesFormula() =>
        Disp(Seq(Equal(Iterate(D(3, 1)), InitialState()), Dot));

    private static Formula NoEarlyReturnFormula()
    {
        Formula k = F.Id("k");
        return Disp(Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Call("Fin", D(3, 0)), Comma, Sp,
            NotEqual(Iterate(Sum(Call("val", k), D(1))), InitialState()), Dot));
    }

    private static Formula OrbitReadoffFormula()
    {
        Formula r = F.Id("r");
        Formula outside = Negated(Member(Call("val", r), ExceptionalSet()));
        Formula firstCoordinate = Call("x0", Iterate(Call("val", r)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, r, Sp, InMacro, Sp, Call("Fin", D(3, 1)), Comma),
            Seq(Parenthesized(outside), Sp, Rightarrow),
            Seq(Equal(firstCoordinate, D(1)), Dot),
        ]));
    }

    private static Formula OddnessFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");

        return Disp(new Formula.Aligned([
            ParameterRow(a, u),
            Seq(Parenthesized(Assumptions(a, u)), Sp, Rightarrow),
            Seq(OddClause(u), Dot),
        ]));
    }

    private static Formula WholeAtomFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");

        return Disp(new Formula.Aligned([
            ParameterRow(a, u),
            Seq(Parenthesized(Assumptions(a, u)), Sp, Rightarrow),
            Parenthesized(OddClause(u)),
            Seq(Land, Sp, Parenthesized(ZeroClause(u)), Dot),
        ]));
    }

    private static Formula ParameterRow(Formula a, Formula u) =>
        Seq(
            Forall, Sp, a, Colon, Sp, FunctionType(Call("Fin", D(5)), Integers()),
            Comma, Sp, u, Colon, Sp, FunctionType(Naturals(), Integers()), Comma);

    private static Formula Assumptions(Formula a, Formula u) =>
        Conjunction(
            IsSolution(a, u),
            CoefficientCongruence(a),
            InitialCongruence(u));

    private static Formula IsSolution(Formula a, Formula u) =>
        Call("IsSolution", Recurrence(a), u);

    private static Formula CoefficientCongruence(Formula a) =>
        Equal(
            CastTuple(a),
            Tuple(D(1), D(0), D(0), D(1), D(0)));

    private static Formula InitialCongruence(Formula u) =>
        Equal(
            CastTuple(u),
            Tuple(D(1), D(0), D(0), D(0), D(0)));

    private static Formula CastTuple(Formula sequence) =>
        Tuple(
            CastModTwo(Sub(sequence, D(0))),
            CastModTwo(Sub(sequence, D(1))),
            CastModTwo(Sub(sequence, D(2))),
            CastModTwo(Sub(sequence, D(3))),
            CastModTwo(Sub(sequence, D(4))));

    private static Formula OddClause(Formula u)
    {
        Formula n = F.Id("n");
        Formula outside = Negated(Member(new Formula.Modulo(n, D(3, 1)), ExceptionalSet()));
        return Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Parenthesized(outside), Sp, Rightarrow, Sp,
            Call("Odd", Sub(u, n)));
    }

    private static Formula ZeroClause(Formula u)
    {
        Formula n = F.Id("n");
        return Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Parenthesized(Equal(Sub(u, n), D(0))), Sp, Rightarrow, Sp,
            Member(new Formula.Modulo(n, D(3, 1)), ExceptionalSet()));
    }

    private static Formula ExceptionalSet() =>
        new Formula.SetLiteral([
            D(1), D(2), D(3), D(4), D(6), D(8), D(1, 2), D(1, 5),
            D(1, 6), D(1, 7), D(2, 3), D(2, 4), D(2, 7), D(2, 9), D(3, 0),
        ]);

    private static Formula InitialState() => Tuple(D(1), D(0), D(0), D(0), D(0));

    private static Formula Iterate(Formula exponent) =>
        Call("iterate", F.Id("step"), exponent, InitialState());

    private static Formula Recurrence(Formula coefficients) =>
        Call("intRecurrence", coefficients);

    private static Formula CastModTwo(Formula value) =>
        Call("cast", value, Call("ZMod", D(2)));

    private static Formula FunctionType(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Sum(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Projection(Formula value, string field) =>
        Seq(value, Dot, F.Id(field));

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Negated(Formula value) =>
        Seq(Neg, Sp, Parenthesized(value));

    private static Formula Conjunction(Formula first, params Formula[] rest) =>
        Joined([first, .. rest], Land);

    private static Formula Tuple(params Formula[] values) =>
        Parenthesized(Joined(values, Comma));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Joined(arguments, Comma)));
}
