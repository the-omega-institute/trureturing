using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LerchSomosLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Recurrence/LerchSomosLimit";

    private static LibraryNoteRef SourceNote =>
        LibraryNoteRef.Create("D5/L/meijer2016a112302");

    private static LibraryNoteRef LerchNote =>
        LibraryNoteRef.Create("D5/L/weisstein2026lerch");

    private static LibraryNoteRef CoffeyNote =>
        LibraryNoteRef.Create("D5/L/coffey2015somosseries");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RealSequence => Seq(Naturals, To, Reals);
    private static Formula S => F.Id("s");
    private static Formula J => F.Id("j");
    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");
    private static Formula A => F.Id("a");

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Invoke(string name, Formula value) => Seq(Named(name), Paren(value));
    private static Formula CastReal(Formula value) => Paren(Seq(value, Colon, Reals));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Colon, domain, Comma, Sp, body);
    private static Formula LambdaOnNaturals(Formula body) =>
        Paren(Seq(J, Colon, Naturals, Mapsto, body));
    private static Formula TsumOnNaturals(Formula body) =>
        Seq(Sum, Apos, Underscore, Grp(J, Colon, Naturals), Sp, body);
    private static Formula SummableOnNaturals(Formula body) =>
        Seq(Named("Summable"), LambdaOnNaturals(body));
    private static Formula KernelTerm =>
        new Formula.Fraction(
            new Formula.Power(CastReal(new Formula.Fraction(D(1), D(2))), J),
            new Formula.Power(Paren(Seq(CastReal(J), Plus, D(1))), S));
    private static Formula LogarithmicTerm =>
        new Formula.Fraction(
            Seq(Named("Real"), Dot, Named("log"), Paren(Seq(CastReal(J), Plus, D(1)))),
            new Formula.Power(CastReal(D(2)), Seq(J, Plus, D(1))));
    private static Formula ConstantName => Named("SomosConstant");
    private static Formula SourcePredicate => Invoke("LPSource", A);
    private static Formula FinValue => Seq(K, Dot, Seq(Mathrm, Grp(F.Id("val"))));
    private static Formula SequenceAt(Formula index) => Seq(A, Paren(index));

    private static Formula KernelDefinition => All(S, Naturals,
        Seq(Invoke("LerchKernel", S), Eq, TsumOnNaturals(KernelTerm)));

    private static Formula ConstantDefinition => Seq(
        ConstantName, Eq, Named("Real"), Dot, Named("exp"),
        Paren(TsumOnNaturals(LogarithmicTerm)));

    private static Formula SourceDefinition => All(A, RealSequence,
        Seq(SourcePredicate, Iff, Paren(Seq(
            SequenceAt(D(0)), Eq, D(1), Sp, Land, Sp,
            Paren(All(N, Naturals, Seq(
                D(0), Lt, N, Implies, Sp,
                SequenceAt(N), Eq,
                new Formula.Fraction(D(1), CastReal(N)), Cdot, Sp,
                Seq(Sum, Underscore, Grp(K, Colon, Named("Fin"), Sp, N), Sp,
                    Invoke("LerchKernel", Seq(N, Minus, FinValue)), Cdot, Sp,
                    SequenceAt(FinValue)))))))));

    private static Formula KernelSummability => All(S, Naturals,
        Seq(D(0), Lt, S, Implies, Sp, SummableOnNaturals(KernelTerm)));

    private static Formula SourceExistsUniquely => Seq(
        Exists, Bang, Sp, A, Colon, RealSequence, Comma, Sp, SourcePredicate);

    private static Formula SourceLimit => All(A, RealSequence,
        Seq(SourcePredicate, Implies, Sp,
            Named("Filter"), Dot, Named("Tendsto"),
            Paren(Seq(A, Comma, Named("Filter"), Dot, Named("atTop"), Comma,
                Invoke("nhds", ConstantName)))));

    private static Formula FullResult => new Formula.Logic(
        Paren(KernelSummability), FormulaLogicOperator.And,
        new Formula.Logic(
            SummableOnNaturals(LogarithmicTerm), FormulaLogicOperator.And,
            new Formula.Logic(
                Paren(SourceExistsUniquely), FormulaLogicOperator.And,
                Paren(SourceLimit))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Lerch convolution source, its summability and unique existence, and its limit at the Somos constant.",
        H("The Lerch Recurrence and the Somos Constant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lerch-kernel"),
                DeclarationHandle.Create(Module + ".LerchKernel"),
                H("The Lerch kernel at one half"),
                StatementSource.FromAuthor(Disp(KernelDefinition)),
                AssessedProvenance.FromLiterature(LerchNote),
                Blocks(Paragraph(Text(
                    "The classical Lerch series at first argument one half and third argument one "
                    + "defines a real kernel for every natural exponent. Equation (1) of the "
                    + "source gives the series, and equation (6) identifies its normalization as "
                    + "twice the polylogarithm at one half. The summation index starts at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("somos-constant"),
                DeclarationHandle.Create(Module + ".SomosConstant"),
                H("The real Somos constant"),
                StatementSource.FromAuthor(Disp(ConstantDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The exponential of this logarithmic sum specifies the real constant whose "
                    + "decimal expansion is A112302. The zero-indexed expression includes the "
                    + "vanishing logarithm of one. The entry's FORMULA section gives the "
                    + "logarithmic expression and the infinite product as published identities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lerch-lp-source"),
                DeclarationHandle.Create(Module + ".LPSource"),
                H("The initial value and linear convolution recurrence"),
                StatementSource.FromAuthor(Disp(SourceDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The initial value is one. At each positive natural index, the recurrence "
                    + "uses every preceding index exactly once. A finite index k has natural "
                    + "value k.val strictly below n, so the kernel exponent is positive. "
                    + "All scalar arithmetic and sequence values are real; the subtraction "
                    + "in the kernel exponent is natural subtraction. This is the LP "
                    + "recurrence in the conjecture's COMMENTS paragraph."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lerch-somos-limit-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Summability, unique source, and the Somos limit"),
                StatementSource.FromAuthor(Disp(FullResult)),
                AssessedProvenance.FromRepo(SourceNote, LerchNote, CoffeyNote),
                Blocks(
                    Paragraph(Text(
                        "The statement has four conjuncts: summability of the kernel series "
                        + "at every positive natural exponent, summability of the logarithmic "
                        + "constant series, unique existence of a total real sequence satisfying "
                        + "the initial value and recurrence, and convergence of every such "
                        + "sequence to the specified real constant.")),
                    Paragraph(Text(
                        "The limit uses the atTop filter on the natural numbers and the real "
                        + "neighborhood filter. Thus every positive real tolerance must hold "
                        + "at all sufficiently large natural indices. The two summability "
                        + "clauses give the infinite sums their convergent-series meaning, "
                        + "and the unique-existence clause supplies the source sequence.")),
                    Paragraph(Text(
                        "The proof constructs the source by strong recursion. Subtracting one "
                        + "from the kernel gives an exponentially bounded nonnegative sequence; "
                        + "its convolution defines nonnegative coefficients bounded by two to "
                        + "the negative index. Their partial sums satisfy the original LP "
                        + "recurrence and hence converge. Differentiating the associated "
                        + "convergent power series identifies the coefficient sum with an "
                        + "exponential. An absolutely summable double series and a weighted "
                        + "logarithmic telescoping sum identify its exponent with the Somos "
                        + "series. This last constant identity is known from Coffey, "
                        + "Proposition 5(b), equation (1.25), specialized to t equal to two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a112302-lerch-somos-limit"),
                    ResolutionKind.Proved)))));
}
