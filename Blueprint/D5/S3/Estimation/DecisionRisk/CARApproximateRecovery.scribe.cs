using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class CARApproximateRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One approximate coarsening-at-random simulation admits a common reverse kernel "
            + "with a signed pairwise recovery budget.",
        H("Approximate CAR recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("car-nonempty-blocks"),
                DeclarationHandle.Create(Prefix + "Block"),
                H("Nonempty blocks"),
                StatementSource.FromAuthor(BlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The output alphabet consists of all nonempty finite subsets of the state "
                        + "space. Blocks of zero weight remain in the alphabet."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("car-probability-row"),
                DeclarationHandle.Create(Prefix + "row"),
                H("CAR rows"),
                StatementSource.FromAuthor(RowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A state assigns weight w(B) to a block containing it and zero to every "
                        + "other block. Nonnegative weights and unit row sums make these probability rows."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("car-pair-weight"),
                DeclarationHandle.Create(Prefix + "pair"),
                H("Pairwise block weights"),
                StatementSource.FromAuthor(PairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pair weight sums the weights of blocks containing both states; the "
                        + "definition also includes equal states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("car-approximate-recovery"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Common reverse kernel and signed recovery bound"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state space A is finite and nonempty, with decidable equality. Both "
                            + "profiles have nonnegative weights and unit row sums. The one forward "
                            + "Markov kernel H is shared by every state, and the existentially "
                            + "quantified reverse kernel R is shared by all conclusions. Kernel "
                            + "arguments are ordered as input then output. Total variation is half "
                            + "the sum of absolute coordinate differences.")),
                    Paragraph(Text(
                        "Delta is signed: it is the pair weight for v minus the pair weight for w. "
                            + "Only Delta(i,j) + epsilon(i) + epsilon(j) is asserted nonnegative. "
                            + "The function eta is the maximum absolute off-diagonal pair difference, "
                            + "with diagonal entries set to zero. Thus eta and each empty row sum "
                            + "are zero on a one-state space, and the recovery error is zero there.")),
                    Paragraph(Text(
                        "The deficiency has target row(w) and source row(v): it measures simulation "
                            + "of w from v. It is the infimum over all reverse Markov kernels of the "
                            + "maximum statewise total-variation error, embedded in the extended "
                            + "nonnegative reals. The bound is truncated at one.")),
                    Paragraph(Text(
                        "For the construction, put F_i(B,C) = row(w,i,B) H(B,C) and "
                            + "Q_i(C) = sum_B F_i(B,C). Multiply each column by "
                            + "a_i(C) = min(1,V_i(C)/Q_i(C)) when Q_i(C) is positive, and by one "
                            + "when it is zero, obtaining t_i. The nonnegative residuals "
                            + "u_i(B) = W_i(B) - sum_C t_i(B,C) and "
                            + "z_i(C) = V_i(C) - sum_B t_i(B,C) both have total mass epsilon(i). "
                            + "For positive epsilon(i), set g_i = t_i + u_i z_i / epsilon(i). "
                            + "When epsilon(i) is zero, both residuals vanish and g_i = t_i; "
                            + "no division by zero is needed.")),
                    Paragraph(Text(
                        "The table g_i has marginals W_i and V_i and is supported on blocks "
                            + "containing i. The overlap of g_i and g_j is at least "
                            + "pair(w,i,j) - epsilon(i) - epsilon(j). Consequently their columnwise "
                            + "half-L1 difference, summed over columns containing both states, is "
                            + "at most the signed budget Delta(i,j) + epsilon(i) + epsilon(j).")),
                    Paragraph(Text(
                        "For v(C) > 0 choose R(C,B) = sum_{j in C} g_j(B,C) / (|C| v(C)). "
                            + "For v(C) = 0 choose a point mass at one fixed singleton block; "
                            + "such columns carry no mass under any V_i. Averaging the tables "
                            + "on C and using |C| >= 2 for distinct states in C yields the "
                            + "factor one half in the signed row budget.")),
                    Paragraph(Text(
                        "If every epsilon(i) is zero, then g_i = F_i. The very same R reduces "
                            + "on every positive-weight column to the displayed subset formula, "
                            + "and is zero when B is not contained in C. Its zero-weight rows "
                            + "remain arbitrary probability rows. No positive lower bound on "
                            + "block weights and no optimality of the coefficients are assumed."))),
                DescribeRole.Theorem))));

    private static Formula BlockFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B");
        return Disp(Seq(Forall, Sp, Typed(a, Seq(Mathrm, Grp(F.Id("Type")))), Comma, Sp,
            Eqn(Call("Block", a), Seq(OpenBrace, Typed(b, Call("Finset", a)), Sp, Mid, Sp,
                Call("Nonempty", b), CloseBrace)), Dot));
    }

    private static Formula RowFormula()
    {
        Formula a = F.Id("A"), w = F.Id("w"), i = F.Id("i"), b = F.Id("B");
        return Disp(Seq(Forall, Sp, Typed(a, Seq(Mathrm, Grp(F.Id("Type")))), Comma, Sp,
            Call("DecidableEq", a), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(w, Function(Call("Block", a), Real())), Comma, Sp,
            Typed(i, a), Comma, Sp, Typed(b, Call("Block", a)), Comma, RowBreak, Grp(),
            Eqn(Call("row", w, i, b), Cases(At(w, b), Seq(i, Sp, InMacro, Sp, b), D(0))), Dot));
    }

    private static Formula PairFormula()
    {
        Formula a = F.Id("A"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j"), b = F.Id("B");
        return Disp(Seq(Forall, Sp, Typed(a, Seq(Mathrm, Grp(F.Id("Type")))), Comma, Sp,
            Call("Fintype", a), Sp, Rightarrow, Sp, Call("DecidableEq", a), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(w, Function(Call("Block", a), Real())), Comma, Sp,
            Typed(i, a), Comma, Sp, Typed(j, a), Comma, RowBreak, Grp(),
            Eqn(Call("pair", w, i, j), Summation(Typed(b, Call("Block", a)),
                Cases(At(w, b), And(Seq(i, Sp, InMacro, Sp, b), Seq(j, Sp, InMacro, Sp, b)), D(0)))), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A"), w = F.Id("w"), v = F.Id("v"), h = F.Id("H"), r = F.Id("R");
        Formula i = F.Id("i"), j = F.Id("j"), b = F.Id("B"), c = F.Id("C");
        Formula budget = F.Id("b"), eta = F.Id("eta");
        Formula emax = new Formula.Subscript(Varepsilon, F.Id("max"));
        Formula bmax = new Formula.Subscript(budget, F.Id("max"));
        Formula blocks = Call("Block", a), profile = Function(blocks, Real());
        Formula kernel = Call("FiniteMarkovKernel", blocks, blocks);
        Formula ei = At(Varepsilon, i), ej = At(Varepsilon, j);
        Formula dij = At(Delta, i, j);
        Formula signed = Add(dij, ei, ej);
        Formula nminus = Paren(Sub(Call("card", a), D(1)));
        Formula pointwise = Seq(Forall, Sp, Typed(i, a), Comma, Sp,
            LeF(Call("totalVariation", Call("channelOutput", Projection(r), Call("row", v, i)),
                Call("row", w, i)), At(budget, i)));
        Formula zeroError = Seq(
            Paren(Seq(Forall, Sp, Typed(i, a), Comma, Sp, Eqn(ei, D(0)))),
            Sp, Rightarrow, Sp, Forall, Sp, Typed(b, blocks), Comma, Sp, Typed(c, blocks), Comma, Sp,
            LtF(D(0), At(v, c)), Sp, Rightarrow, Sp,
            Eqn(At(Projection(r), c, b), Cases(
                Div(Mul(Call("card", b), Paren(Mul(At(w, b), At(Projection(h), b, c)))),
                    Mul(Call("card", c), At(v, c))),
                Seq(b, Sp, Subseteq, Sp, c), D(0))));
        Formula conclusion = Seq(Exists, Sp, Typed(r, kernel), Comma, RowBreak, Grp(),
            And(
                Seq(Forall, Sp, Typed(i, a), Comma, Sp, Typed(j, a), Comma, Sp, LeF(D(0), signed)),
                pointwise,
                LeF(Call("finiteDeficiency", Call("row", w), Call("row", v)),
                    Call("ofReal", Call("min", D(1), bmax))),
                LeF(Call("min", D(1), bmax), Call("min", D(1),
                    Add(Div(Mul(nminus, eta), D(2)), Mul(nminus, emax)))),
                zeroError));
        Formula definitions = Seq(
            F.Text, Grp(F.Id("let")), Sp,
            Eqn(Varepsilon, Seq(i, Sp, Mapsto, Sp,
                Call("totalVariation", Call("channelOutput", Projection(h), Call("row", w, i)),
                    Call("row", v, i)))), Comma, RowBreak, Grp(),
            Eqn(Delta, Seq(i, Sp, j, Sp, Mapsto, Sp,
                Sub(Call("pair", v, i, j), Call("pair", w, i, j)))), Comma, RowBreak, Grp(),
            Eqn(budget, Seq(i, Sp, Mapsto, Sp, Mul(Div(D(1), D(2)),
                Summation(Seq(j, Sp, InMacro, Sp, a, Comma, Sp, j, Sp, Neq, Sp, i), Paren(signed))))),
            Comma, RowBreak, Grp(),
            Eqn(emax, Maximum(Seq(i, Sp, InMacro, Sp, a), ei)), Comma, Sp,
            Eqn(eta, Maximum(Seq(i, Comma, j, Sp, InMacro, Sp, a),
                Cases(D(0), Eqn(i, j), Seq(Lvert, dij, Rvert)))), Comma, Sp,
            Eqn(bmax, Maximum(Seq(i, Sp, InMacro, Sp, a), At(budget, i))),
            RowBreak, Grp(), F.Text, Grp(F.Id("in")), Sp, conclusion);
        Formula hypotheses = And(
            Seq(Forall, Sp, Typed(b, blocks), Comma, Sp, LeF(D(0), At(w, b))),
            Seq(Forall, Sp, Typed(c, blocks), Comma, Sp, LeF(D(0), At(v, c))),
            Seq(Forall, Sp, Typed(i, a), Comma, Sp,
                Eqn(Summation(Typed(b, blocks), Call("row", w, i, b)), D(1))),
            Seq(Forall, Sp, Typed(i, a), Comma, Sp,
                Eqn(Summation(Typed(c, blocks), Call("row", v, i, c)), D(1))));
        return Disp(Seq(
            Forall, Sp, Typed(a, Seq(Mathrm, Grp(F.Id("Type")))), Comma, Sp,
            Call("Fintype", a), Sp, Rightarrow, Sp, Call("DecidableEq", a), Sp, Rightarrow, Sp,
            Call("Nonempty", a), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(w, profile), Comma, Sp, Typed(v, profile), Comma, Sp,
            Typed(h, kernel), Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(), definitions, Dot));
    }

    private static Formula Call(string name, params Formula[] args) => At(Seq(Operatorname, Grp(F.Id(name))), args);

    private static Formula At(Formula function, params Formula[] args)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Cases(Formula yes, Formula condition, Formula no) => Seq(
        Begin, Grp(F.Id("cases")), yes, Amp, condition, RowBreak,
        no, Amp, F.Text, Grp(F.Id("otherwise")), End, Grp(F.Id("cases")));

    private static Formula And(params Formula[] clauses) => Paren(Infix(Land, clauses));
    private static Formula Add(params Formula[] terms) => Infix(Plus, terms);
    private static Formula Sub(params Formula[] terms) => Infix(Minus, terms);
    private static Formula Mul(params Formula[] terms) => Infix(Cdot, terms);

    private static Formula Infix(Formula op, Formula[] terms)
    {
        var items = new List<Formula>();
        for (var index = 0; index < terms.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, op, Sp]);
            items.Add(Paren(terms[index]));
        }

        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Function(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Projection(Formula value) => Seq(value, Dot, D(1));
    private static Formula Summation(Formula index, Formula body) => Seq(new Formula.Subscript(Sum, Grp(index)), Sp, Grp(body));
    private static Formula Maximum(Formula index, Formula body) => Seq(new Formula.Subscript(Max, Grp(index)), Sp, Grp(body));
    private static Formula Div(Formula numerator, Formula denominator) => Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LtF(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LeF(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
}
