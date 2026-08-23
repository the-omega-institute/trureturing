using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class PeriodicImpliesQuadraticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eventually periodic continued fractions yield nondegenerate quadratic equations through integer Mobius transfers.",
        H("Periodic Continued Fractions Are Quadratic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cross-multiplied-transfers-compose"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.rel_comp"),
                H("Cross-multiplied transfers compose"),
                StatementSource.FromAuthor(RelCompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If one integer linear-fractional transfer relates x to an intermediate "
                        + "value z and a second relates z to y, their matrix product relates x "
                        + "directly to y. The relation is cross-multiplied, so composition uses "
                        + "no division and assumes no denominator is nonzero."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("segment-relates-complete-quotient-endpoints"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_rel"),
                H("A segment relates its endpoint complete quotients"),
                StatementSource.FromAuthor(SegmentRelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product of any consecutive block of inverse continued-fraction steps "
                        + "relates the complete quotient at the start of the block to the complete "
                        + "quotient at its end. This packages repeated inverse-step recurrence into "
                        + "one integer transfer matrix."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("transfer-determinant-is-multiplicative"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.det_comp"),
                H("The transfer determinant is multiplicative"),
                StatementSource.FromAuthor(DeterminantCompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant of the product transfer is the product of the two integer "
                        + "determinants. This is the usual two-by-two determinant identity written "
                        + "for the four-entry transfer representation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("segment-has-alternating-determinant"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_det"),
                H("A segment has alternating determinant"),
                StatementSource.FromAuthor(SegmentDeterminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each inverse continued-fraction step has determinant minus one. Therefore a "
                        + "segment of the given length has determinant minus one to that length, "
                        + "and in particular every segment transfer is nondegenerate."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nonnegative-coefficients-give-nonnegative-entries"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_entries_nonneg"),
                H("Nonnegative coefficients give nonnegative segment entries"),
                StatementSource.FromAuthor(SegmentEntriesNonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every coefficient in a finite block is nonnegative, all four entries of "
                        + "its transfer matrix are nonnegative. The property is preserved as each "
                        + "inverse-step matrix is multiplied onto the remaining segment."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("positive-coefficients-give-positive-upper-right-entry"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_b_pos"),
                H("Positive coefficients make the upper-right entry positive"),
                StatementSource.FromAuthor(SegmentUpperRightPositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonempty segment whose coefficients are all positive has a strictly positive "
                        + "upper-right matrix entry. Positivity propagates from the first step, while "
                        + "nonnegativity of the other tail entries prevents cancellation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("period-block-has-positive-upper-right-entry"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.period_segment_b_pos"),
                H("A periodic block has positive upper-right entry"),
                StatementSource.FromAuthor(PeriodSegmentUpperRightPositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certified period has positive length, and every coefficient from the "
                        + "period start onward is positive. Applying the finite-segment positivity "
                        + "result makes the upper-right entry of the period transfer strictly positive."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("computed-infinite-fraction-is-irrational"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.computed_cf_irrational"),
                H("The computed infinite continued fraction is irrational"),
                StatementSource.FromAuthor(ComputedFractionIrrationalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A certified coefficient is present at every position of the computed continued "
                        + "fraction. A rational real would instead have a terminating regular continued "
                        + "fraction, so the two properties are incompatible and the represented value "
                        + "must be irrational."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("quadratic-equations-transfer-across-segments"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.quadratic_transfers_across_segment"),
                H("Quadratic equations transfer across nondegenerate segments"),
                StatementSource.FromAuthor(QuadraticTransferFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose a nondegenerate integer transfer relates x to y and y satisfies a "
                        + "nonzero integer quadratic equation. Clearing the linear-fractional relation "
                        + "produces an integer quadratic equation for x. The nonzero determinant "
                        + "ensures that its three transformed coefficients cannot all vanish."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("eventual-periodicity-forces-quadratic-irrationality"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.eventually_periodic_cf_implies_quadratic_irrational"),
                H("Eventual periodicity forces quadratic irrationality"),
                StatementSource.FromAuthor(EventualPeriodicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Repeating the complete quotient makes the period transfer fix the periodic "
                            + "tail. Cross-multiplication gives that tail a nonzero integer quadratic "
                            + "equation, with nonvanishing certified by the positive upper-right entry.")),
                    Paragraph(Text(
                        "The prefix transfer has determinant plus or minus one, so the quadratic "
                            + "equation pulls back from the periodic tail to the original value. The "
                            + "infinite computed coefficient stream separately proves irrationality, "
                            + "giving Lagrange direction A."))),
                DescribeRole.Theorem))));

    private static Formula RelCompositionFormula()
    {
        Formula matrixM = F.Id("M");
        Formula matrixN = F.Id("N");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");

        return Disp(Seq(
            Forall, Sp, matrixM, Comma, Sp, matrixN, Sp, InMacro, Sp, MobiusMatrices(),
            Comma, Sp, x, Comma, Sp, y, Comma, Sp, z, Sp, InMacro, Sp, RealNumbers(),
            Comma, Esc,
            Open, Rel(matrixM, x, z), Sp, Land, Sp, Rel(matrixN, z, y), Close,
            Sp, Rightarrow, Sp, Rel(Comp(matrixM, matrixN), x, y)));
    }

    private static Formula SegmentRelationFormula()
    {
        Formula x = F.Id("x");
        Formula h = F.Id("h");
        Formula first = F.Id("first");
        Formula length = F.Id("length");
        Formula endpoint = Seq(first, Sp, Plus, Sp, length);
        Formula matrix = Segment(Coefficient(h), first, length);

        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            h, Colon, Sp, Call("EventuallyPeriodicCF", x), Comma, Sp,
            first, Comma, Sp, length, Sp, InMacro, Sp, NaturalNumbers(), Comma, Esc,
            Rel(matrix, Quotient(h, first), Quotient(h, endpoint))));
    }

    private static Formula DeterminantCompositionFormula()
    {
        Formula matrixM = F.Id("M");
        Formula matrixN = F.Id("N");

        return Disp(Seq(
            Forall, Sp, matrixM, Comma, Sp, matrixN, Sp, InMacro, Sp, MobiusMatrices(),
            Comma, Esc, Det(Comp(matrixM, matrixN)), Sp, Eq, Sp,
            Det(matrixM), Sp, Cdot, Sp, Det(matrixN)));
    }

    private static Formula SegmentDeterminantFormula()
    {
        Formula coefficient = F.Id("coefficient");
        Formula first = F.Id("first");
        Formula length = F.Id("length");

        return Disp(Seq(
            Forall, Sp, coefficient, Colon, Sp, NaturalNumbers(), Sp, To, Sp, Integers(),
            Comma, Sp, first, Comma, Sp, length, Sp, InMacro, Sp, NaturalNumbers(),
            Comma, Esc, Det(Segment(coefficient, first, length)), Sp, Eq, Sp,
            Open, Minus, D(1), Close, Caret, Grp(length)));
    }

    private static Formula SegmentEntriesNonnegativeFormula()
    {
        Formula coefficient = F.Id("coefficient");
        Formula first = F.Id("first");
        Formula length = F.Id("length");
        Formula k = F.Id("k");
        Formula matrix = Segment(coefficient, first, length);
        Formula indexedCoefficient = Call("coefficient", Seq(first, Sp, Plus, Sp, k));

        return Disp(Seq(
            Forall, Sp, coefficient, Colon, Sp, NaturalNumbers(), Sp, To, Sp, Integers(),
            Comma, Sp, first, Comma, Sp, length, Sp, InMacro, Sp, NaturalNumbers(),
            Comma, Esc,
            OpenBracket, Forall, Sp, k, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            k, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, indexedCoefficient, CloseBracket,
            Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, Call("a", matrix), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, Call("b", matrix), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, Call("c", matrix), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, Call("d", matrix)));
    }

    private static Formula SegmentUpperRightPositiveFormula()
    {
        Formula coefficient = F.Id("coefficient");
        Formula first = F.Id("first");
        Formula length = F.Id("length");
        Formula k = F.Id("k");
        Formula matrix = Segment(coefficient, first, length);
        Formula indexedCoefficient = Call("coefficient", Seq(first, Sp, Plus, Sp, k));

        return Disp(Seq(
            Forall, Sp, coefficient, Colon, Sp, NaturalNumbers(), Sp, To, Sp, Integers(),
            Comma, Sp, first, Comma, Sp, length, Sp, InMacro, Sp, NaturalNumbers(),
            Comma, Esc,
            Open, D(0), Sp, Lt, Sp, length, Sp, Land, Sp,
            OpenBracket, Forall, Sp, k, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            k, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, indexedCoefficient, CloseBracket, Close,
            Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp, Call("b", matrix)));
    }

    private static Formula PeriodSegmentUpperRightPositiveFormula()
    {
        Formula x = F.Id("x");
        Formula h = F.Id("h");
        Formula matrix = Segment(Coefficient(h), Start(h), Period(h));

        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            h, Colon, Sp, Call("EventuallyPeriodicCF", x), Comma, Esc,
            D(0), Sp, Lt, Sp, Call("b", matrix)));
    }

    private static Formula ComputedFractionIrrationalFormula()
    {
        Formula x = F.Id("x");
        Formula h = F.Id("h");

        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            h, Colon, Sp, Call("EventuallyPeriodicCF", x), Comma, Esc,
            Call("Irrational", x)));
    }

    private static Formula QuadraticTransferFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula matrix = F.Id("M");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            matrix, Sp, InMacro, Sp, MobiusMatrices(), Comma, Sp,
            u, Comma, Sp, v, Comma, Sp, w, Sp, InMacro, Sp, Integers(), Comma, Esc,
            Open,
            Det(matrix), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Rel(matrix, x, y), Sp, Land, Sp,
            NonzeroTriple(u, v, w), Sp, Land, Sp,
            Polynomial(u, v, w, y), Sp, Eq, Sp, D(0),
            Close, Sp, Rightarrow, Sp,
            Exists, Sp, a, Comma, Sp, b, Comma, Sp, c, Sp, InMacro, Sp, Integers(),
            Comma, Esc, NonzeroTriple(a, b, c), Sp, Land, Sp,
            Polynomial(a, b, c, x), Sp, Eq, Sp, D(0)));
    }

    private static Formula EventualPeriodicityFormula()
    {
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");

        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            Call("EventuallyPeriodicCF", x), Sp, Rightarrow, Sp,
            Open,
            Call("Irrational", x), Sp, Land, Sp,
            Exists, Sp, a, Comma, Sp, b, Comma, Sp, c, Sp, InMacro, Sp, Integers(),
            Comma, Esc, NonzeroTriple(a, b, c), Sp, Land, Sp,
            Polynomial(a, b, c, x), Sp, Eq, Sp, D(0),
            Close));
    }

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula NaturalNumbers() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula MobiusMatrices() =>
        Seq(Operatorname, Grp(F.Id("MobiusInt")));

    private static Formula Rel(Formula matrix, Formula source, Formula target) =>
        Call("Rel", matrix, source, target);

    private static Formula Comp(Formula first, Formula second) =>
        Call("comp", first, second);

    private static Formula Det(Formula matrix) => Call("det", matrix);

    private static Formula Segment(Formula coefficient, Formula first, Formula length) =>
        Call("segment", coefficient, first, length);

    private static Formula Coefficient(Formula certificate) =>
        Call("coefficient", certificate);

    private static Formula Quotient(Formula certificate, Formula index) =>
        Call("completeQuotient", certificate, index);

    private static Formula Start(Formula certificate) => Call("start", certificate);

    private static Formula Period(Formula certificate) => Call("period", certificate);

    private static Formula NonzeroTriple(Formula first, Formula second, Formula third) =>
        Seq(Open,
            first, Sp, Neq, Sp, D(0), Sp, Lor, Sp,
            second, Sp, Neq, Sp, D(0), Sp, Lor, Sp,
            third, Sp, Neq, Sp, D(0), Close);

    private static Formula Polynomial(
        Formula leading,
        Formula linear,
        Formula constant,
        Formula value) =>
        Seq(
            leading, Sp, Cdot, Sp, value, Caret, Grp(D(2)), Sp, Plus, Sp,
            linear, Sp, Cdot, Sp, value, Sp, Plus, Sp, constant);
}
