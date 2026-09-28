using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EventualClickDoobInstrumentDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/EventualClickDoobInstrument.eventual_click_doob_instrument";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The support Doob transform realizes finite click branches conditioned on eventual detection.",
        H("The Eventual-Click Doob Instrument"),
        Blocks(Describe.Lean(
            DescribeId.Create("eventual-click-doob-instrument"),
            DeclarationHandle.Create(Declaration),
            H("Conditioning on an eventual click"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Q be the no-click Kraus family and L the click Kraus family of a complete finite-dimensional "
                        + "instrument. If the survival effects converge to F, then the residual effect R = I - F "
                        + "satisfies the one-step balance law. Every click Kraus operator vanishes on the orthogonal "
                        + "complement of the support P of R, and P Q (I - P) = 0 for every no-click Kraus operator. "
                        + "Consequently the no-click pullback maps operators supported on P to operators supported "
                        + "on P, and every click pullback is supported on P.")),
                Paragraph(Text(
                    "The square root G of R and its support pseudo-inverse Gplus obey Gplus G = G Gplus = P and "
                        + "P G = G. Conjugating the no-click channel and pulling back the click maps by Gplus gives "
                        + "the displayed Kraus families, completeness on P, and both intertwining identities.")),
                Paragraph(Text(
                    "For a density state with positive residual weight r, the transformed branch at every positive "
                        + "time equals the original click branch divided by r. Its trace has the same likelihood-ratio "
                        + "form, and whenever that trace is nonzero the two normalized terminal states coincide."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), alpha = F.Id("alpha"), xi = F.Id("xi"), beta = F.Id("beta");
        Formula a = F.Id("a"), x = F.Id("x"), b = F.Id("b"), n = F.Id("n");
        Formula h = F.Id("H"), z = F.Id("Z"), state = Rho, variable = F.Id("X");
        Formula q = F.Id("Q"), l = F.Id("L"), eff = F.Id("F"), identity = F.Id("I");
        Formula noClick = F.Id("N"), click = F.Id("C"), residual = F.Id("R");
        Formula support = F.Id("P"), root = F.Id("G"), inverseRoot = F.Id("Gplus");
        Formula transformedNoClick = F.Id("Ntilde"), transformedClick = F.Id("Ctilde");
        Formula rhoMatrix = F.Id("rhoMatrix"), weight = F.Id("r");
        Formula original = F.Id("original"), conditioned = F.Id("conditioned");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finD = Call("Fin", d);
        Formula matrix = Call("Matrix", finD, finD, complexes);
        Formula zero = D(0);

        Formula qAt(Formula index) => Call("Q", index);
        Formula lAt(Formula outcome, Formula index) => Call("L", outcome, index);
        Formula nAt(Formula input) => Call("N", input);
        Formula cAt(Formula outcome, Formula input) => Call("C", outcome, input);
        Formula ntAt(Formula input) => Call("Ntilde", input);
        Formula ctAt(Formula outcome, Formula input) => Call("Ctilde", outcome, input);
        Formula dualQ(Formula input) => Call("noClickDual", q, input);
        Formula dualL(Formula outcome, Formula input) => Call("noClickDual", Call("L", outcome), input);

        Formula completenessHypothesis = Seq(
            Sum, Underscore, Grp(a, Sp, InMacro, Sp, alpha), Sp,
            Product(Adjoint(qAt(a)), qAt(a)), Sp, Plus, Sp,
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, xi), Sp,
            Sum, Underscore, Grp(b, Sp, InMacro, Sp, beta), Sp,
            Product(Adjoint(lAt(x, b)), lAt(x, b)), Sp, Eq, Sp, identity);
        Formula survivalLimit = Seq(
            Lim, Underscore, Grp(n, Sp, To, Sp, Infty), Sp,
            Call("survival", q, n), Sp, Eq, Sp, eff);

        Formula noClickDefinition = Lambda(variable, Seq(
            Sum, Underscore, Grp(a, Sp, InMacro, Sp, alpha), Sp,
            Product(qAt(a), variable, Adjoint(qAt(a)))));
        Formula clickDefinition = Lambda(Seq(x, Comma, Sp, variable), Seq(
            Sum, Underscore, Grp(b, Sp, InMacro, Sp, beta), Sp,
            Product(lAt(x, b), variable, Adjoint(lAt(x, b)))));
        Formula residualDefinition = Parenthesized(Seq(identity, Sp, Minus, Sp, eff));
        Formula supportDefinition = Call("spectralSupport", residual);
        Formula rootDefinition = Call("cfc", Lambda(F.Id("t"), Call("sqrt", F.Id("t"))), residual);
        Formula inverseRootDefinition = Call("spectralInverseSqrt", residual);
        Formula transformedNoClickDefinition = Lambda(variable,
            Product(root, nAt(Product(inverseRoot, variable, inverseRoot)), root));
        Formula transformedClickDefinition = Lambda(Seq(x, Comma, Sp, variable),
            cAt(x, Product(inverseRoot, variable, inverseRoot)));

        Formula balance = Seq(
            residual, Sp, Eq, Sp, dualQ(residual), Sp, Plus, Sp,
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, xi), Sp, dualL(x, identity));
        Formula qSupport = Seq(
            Forall, Sp, a, Sp, InMacro, Sp, alpha, Comma, Sp,
            Product(support, qAt(a), Parenthesized(Seq(identity, Sp, Minus, Sp, support))),
            Sp, Eq, Sp, zero);
        Formula lSupport = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, xi, Comma, Sp,
            Forall, Sp, b, Sp, InMacro, Sp, beta, Comma, Sp,
            Product(lAt(x, b), Parenthesized(Seq(identity, Sp, Minus, Sp, support))),
            Sp, Eq, Sp, zero);
        Formula qDualSupport = Seq(
            Forall, Sp, Typed(h, matrix), Comma, Sp,
            Parenthesized(Seq(h, Sp, Eq, Sp, Product(support, h, support))),
            Sp, Rightarrow, Sp,
            Parenthesized(Seq(dualQ(h), Sp, Eq, Sp, Product(support, dualQ(h), support))));
        Formula lDualSupport = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, xi, Comma, Sp,
            Forall, Sp, Typed(z, matrix), Comma, Sp,
            dualL(x, z), Sp, Eq, Sp, Product(support, dualL(x, z), support));
        Formula inverseLeft = Seq(Product(inverseRoot, root), Sp, Eq, Sp, support);
        Formula inverseRight = Seq(Product(root, inverseRoot), Sp, Eq, Sp, support);
        Formula supportRoot = Seq(Product(support, root), Sp, Eq, Sp, root);

        Formula noClickKraus = Seq(
            Forall, Sp, Typed(variable, matrix), Comma, Sp,
            ntAt(variable), Sp, Eq, Sp,
            Sum, Underscore, Grp(a, Sp, InMacro, Sp, alpha), Sp,
            Product(KrausNoClick(a, root, inverseRoot), variable,
                Adjoint(KrausNoClick(a, root, inverseRoot))));
        Formula clickKraus = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, xi, Comma, Sp,
            Forall, Sp, Typed(variable, matrix), Comma, Sp,
            ctAt(x, variable), Sp, Eq, Sp,
            Sum, Underscore, Grp(b, Sp, InMacro, Sp, beta), Sp,
            Product(KrausClick(x, b, inverseRoot), variable,
                Adjoint(KrausClick(x, b, inverseRoot))));
        Formula transformedCompleteness = Seq(
            Sum, Underscore, Grp(a, Sp, InMacro, Sp, alpha), Sp,
            Product(Adjoint(KrausNoClick(a, root, inverseRoot)), support,
                KrausNoClick(a, root, inverseRoot)), Sp, Plus, Sp,
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, xi), Sp,
            Sum, Underscore, Grp(b, Sp, InMacro, Sp, beta), Sp,
            Product(Adjoint(KrausClick(x, b, inverseRoot)), KrausClick(x, b, inverseRoot)),
            Sp, Eq, Sp, support);
        Formula noClickIntertwining = Seq(
            Forall, Sp, Typed(variable, matrix), Comma, Sp,
            ntAt(Product(root, variable, root)), Sp, Eq, Sp,
            Product(root, nAt(variable), root));
        Formula clickIntertwining = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, xi, Comma, Sp,
            Forall, Sp, Typed(variable, matrix), Comma, Sp,
            ctAt(x, Product(root, variable, root)), Sp, Eq, Sp, cAt(x, variable));

        Formula rhoMatrixDefinition = Call("ofMatrixSymm", Call("val", state));
        Formula weightDefinition = Seq(Operatorname, Grp(F.Id("Re")), Sp,
            Trace(Product(rhoMatrix, residual)));
        Formula originalDefinition = cAt(x,
            Iterate(noClick, Parenthesized(Seq(n, Sp, Minus, Sp, D(1))), rhoMatrix));
        Formula conditionedInput = Scalar(Inverse(weight), Product(root, rhoMatrix, root));
        Formula conditionedDefinition = ctAt(x,
            Iterate(transformedNoClick, Parenthesized(Seq(n, Sp, Minus, Sp, D(1))), conditionedInput));
        Formula branchEquality = Seq(conditioned, Sp, Eq, Sp, Scalar(Inverse(weight), original));
        Formula traceRatio = Seq(Trace(conditioned), Sp, Eq, Sp,
            Frac(Trace(original), weight));
        Formula normalizedStateEquality = Seq(
            Scalar(Inverse(Trace(conditioned)), conditioned), Sp, Eq, Sp,
            Scalar(Inverse(Trace(original)), original));
        Formula normalizedEquality = Seq(
            Parenthesized(Seq(Trace(original), Sp, Neq, Sp, zero)), Sp, Rightarrow, Sp,
            Parenthesized(Conjunction(
                Seq(Trace(conditioned), Sp, Neq, Sp, zero),
                normalizedStateEquality)));
        Formula densityClause = Seq(
            Forall, Sp, Typed(state, Call("DensityState", finD)), Comma, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            Parenthesized(Seq(D(1), Sp, Leq, Sp, n)), Sp, Rightarrow, Sp,
            Let(rhoMatrix, rhoMatrixDefinition),
            Let(weight, weightDefinition),
            Parenthesized(Seq(zero, Sp, Lt, Sp, weight)), Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Forall, Sp, x, Sp, InMacro, Sp, xi, Comma, Sp,
                Let(original, originalDefinition),
                Let(conditioned, conditionedDefinition),
                Conjunction(branchEquality, traceRatio, normalizedEquality))));

        return Disp(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, naturals, Comma, Sp,
            Typed(alpha, type), Comma, Sp, Typed(xi, type), Comma, Sp, Typed(beta, type), Comma, RowBreak, Grp(),
            OpenBracket, Call("Fintype", alpha), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", xi), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", beta), CloseBracket, Comma, RowBreak, Grp(),
            Typed(q, Arrow(alpha, matrix)), Comma, Sp,
            Typed(l, Arrow(xi, Arrow(beta, matrix))), Comma, Sp,
            Typed(eff, matrix), Comma, RowBreak, Grp(),
            Parenthesized(completenessHypothesis), Sp, Rightarrow, RowBreak, Grp(),
            Parenthesized(survivalLimit), Sp, Rightarrow, RowBreak, Grp(),
            Let(noClick, noClickDefinition),
            Let(click, clickDefinition),
            Let(residual, residualDefinition),
            Let(support, supportDefinition),
            Let(root, rootDefinition),
            Let(inverseRoot, inverseRootDefinition),
            Let(transformedNoClick, transformedNoClickDefinition),
            Let(transformedClick, transformedClickDefinition),
            Conjunction(
                balance, qSupport, lSupport, qDualSupport, lDualSupport,
                inverseLeft, inverseRight, supportRoot, noClickKraus, clickKraus,
                transformedCompleteness, noClickIntertwining, clickIntertwining, densityClause),
            Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Arrow(Formula source, Formula target) => Seq(Grp(source), Sp, To, Sp, target);

    private static Formula Lambda(Formula variables, Formula body) =>
        Parenthesized(Seq(variables, Sp, Mapsto, Sp, body));

    private static Formula Let(Formula name, Formula value) => Seq(
        Operatorname, Grp(F.Id("let")), Sp, name, Sp, Colon, Eq, Sp, value, SemiSpace, RowBreak, Grp());

    private static Formula Product(params Formula[] factors)
    {
        var items = new List<Formula>();
        for (var index = 0; index < factors.Length; index++)
        {
            if (index > 0) items.Add(Sp);
            items.Add(Parenthesized(factors[index]));
        }

        return Seq([.. items]);
    }

    private static Formula Adjoint(Formula value) => Seq(Grp(value), Caret, Grp(Star));

    private static Formula Inverse(Formula value) =>
        Seq(Grp(value), Caret, Grp(Minus, D(1)));

    private static Formula Scalar(Formula scalar, Formula value) =>
        Product(Parenthesized(scalar), value);

    private static Formula Trace(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Tr")), Open, value, Close);

    private static Formula Frac(Formula numerator, Formula denominator) =>
        Seq(F.Frac, Grp(numerator), Grp(denominator));

    private static Formula Iterate(Formula function, Formula exponent, Formula input) =>
        Seq(Grp(function), Caret, Grp(exponent), Open, input, Close);

    private static Formula KrausNoClick(Formula index, Formula root, Formula inverseRoot) =>
        Product(root, Call("Q", index), inverseRoot);

    private static Formula KrausClick(Formula outcome, Formula index, Formula inverseRoot) =>
        Product(Call("L", outcome, index), inverseRoot);

    private static Formula Conjunction(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, RowBreak, Grp()]);
            items.Add(Parenthesized(clauses[index]));
        }

        return Seq([.. items]);
    }
}
